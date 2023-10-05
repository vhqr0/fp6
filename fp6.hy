(require
  hiolib.rule :readers * *)

(import
  time [sleep time]
  math [modf]
  random [getrandbits]
  functools [cached-property]
  collections [deque]
  logging
  logging [getLogger]
  select [select]
  threading [Thread]
  pcap :as pypcap
  scapy.all :as sp
  hiolib.rule *
  hiolib.stream *
  hiolib.util.inet *)

(setv fps (list))
(defn fp-register [fp] (.append fps fp) fp)

(defn idseq-packB [id seq]
  (+ (<< id 8) seq))

(defn idseq-unpackB [x]
  #((>> x 8) (& x 0xff)))

(defn idseq-packH [id seq]
  (+ (<< id 16) seq))

(defn idseq-unpackH [x]
  #((>> x 16) (& x 0xffff)))

(defclass FPCtx []
  (setv logger (getLogger "fp6"))

  (defn #-- init [self dst [iface None] [src None] [next-hop None] [mac-dst None] [mac-src None]
                  [fps fps] [send-attempts 2] [send-interval 0.01] [send-timewait 0.2] [dump-path "fp6"]]
    ;; - id: The id and seq (bots 8 bits) are embedded in the flow
    ;; label of ipv6 and the id and seq of icmpv6 echo request to
    ;; ensure that it can distinguish whether an icmpv6 error message
    ;; or echo reply comes from the process and the corresponding
    ;; probe group.
    ;;
    ;; - iface: The iface is usually determined by the dst, but
    ;; considering that the link-local address may lead to ambiguity,
    ;; it is necessary to manually specify it even when the routing
    ;; table is reliable.
    ;;
    ;; - route: The src and next-hop are usually determined by the dst
    ;; and iface. It is important to note that the src does not affect
    ;; the selection of the iface. Therefore, if the dst is a
    ;; link-local address on the link of the iface A, then iface
    ;; should be specified as iface A instead of specifying the src as
    ;; the link-local address of iface A.
    ;;
    ;; - mac: the mac-dst and mac-src are usually determined by the
    ;; next-hop and iface. It is important to note that root
    ;; privileges are required to reslove the mac-dst.

    (setv self.id            (+ 0x80 (getrandbits 7))
          self.dst           dst
          self.iface         (or iface (get (.route sp.conf.route6 dst) 0)) 
          self.src           (or src (get self.route 1))
          self.next-hop      (or next-hop (get self.route 2))
          self.mac-dst       (or mac-dst (sp.getmacbyip6 (if (= self.next-hop "::") self.dst self.next-hop)))
          self.mac-src       (or mac-src (. (get sp.conf.ifaces self.iface) mac))
          self.fps           (lfor #(seq fp-class) (enumerate fps) (fp-class :ctx self :seq seq))
          self.send-attempts send-attempts
          self.send-interval send-interval
          self.send-timewait send-timewait
          self.dump-path     dump-path))

  (defn [cached-property] route [self]
    (let [route (.route sp.conf.route6 self.dst :dev self.iface)]
      (unless (= (get route 0) self.iface)
        (raise RuntimeError))
      route))

  (defn [property] dump-pcap-path [self]
    (.format "{}.pcap" self.dump-path))

  (defn [property] dump-all-pcap-path [self]
    (.format "{}.all.pcap" self.dump-path))

  (defn log-info [self]
    (for [attr #("iface" "dst" "src" "next-hop" "mac-src" "mac-dst")]
      (.info self.logger "[attr] %s=%s" attr (getattr self (hy.mangle attr))))
    (for [#(seq fp) (enumerate self.fps)]
      (.info self.logger "[fp] seq=%d, name=%s" seq fp.__class__.__name__)))

  (defn prepare [self]
    (for [fp self.fps]
      (.prepare fp))
    (setv self.pcap
          (doto (pypcap.pcap :name self.iface :promisc False :timeout-ms 100)
                (.setdirection pypcap.PCAP-D-IN)
                (.setfilter (.format "ip6 src {}" self.dst)))
          self.packets       (list)
          self.send-finished False
          self.recv-queue    (deque)))

  (defn cleanup [self]
    (.close self.pcap)
    (.sort self.packets :key (fn [x] (get x 0)))
    (with [f (open self.dump-all-pcap-path "wb")]
      (let [writer (PcapWriter (RawIOStream f))]
        (.write-head writer)
        (for [#(ts packet) self.packets]
          (let [#(msec sec) (modf ts)]
            (.write-packet writer packet :sec (int sec) :msec (int (* msec 1,000,000)))))))
    (with [f (open self.dump-pcap-path "wb")]
      (let [writer (PcapWriter (RawIOStream f))]
        (.write-head writer)
        (for [#(seq fp) (enumerate self.fps)]
          (for [probe fp.probes]
            (.write-packet writer probe :sec seq :msec 1))
          (for [answer fp.answers]
            (.write-packet writer answer :sec seq :msec 2))))))

  (defn send-probe [self probe]
    (.append self.packets #((time) probe))
    (.sendpacket self.pcap probe))

  (defn recv-answers [self]
    (for [#(ts answer) (.readpkts self.pcap)]
      (.append self.packets #(ts answer))
      (.append self.recv-queue answer)))

  (defn dispatch-answer [self answer parsed-answer head id seq]
    (when (and (= id self.id) (chainc 0 <= seq < (len self.fps)))
      (let [fp (get self.fps seq)]
        (when (.validate fp head)
          (.append fp.answers answer)
          (.append fp.parsed-answers parsed-answer)))))

  (defn dispatch-answers [self]
    (while self.recv-queue
      (let [answer (.popleft self.recv-queue)
            parsed-answer (Ether.parse answer)
            head (get parsed-answer #(ICMPv6 TCP))]
        (cond (isinstance head ICMPv6)
              (let [icmpv6 head.next-packet]
                (cond (isinstance icmpv6 ICMPv6EchoRep)
                      (let [#(id seq) #(icmpv6.id icmpv6.seq)]
                        (.dispatch-answer self answer parsed-answer head id seq))
                      (isinstance icmpv6 #(ICMPv6DestUnreach ICMPv6ParamProblem))
                      (let [ipv6error icmpv6.next-packet]
                        (when isinstance ipv6error IPv6Error
                          (let [#(id seq) (idseq-unpackB ipv6error.fl)]
                            (.dispatch-answer self answer parsed-answer head id seq))))))
              (isinstance head TCP)
              (let [#(id seq) (idseq-unpackH (- head.ack 1))]
                (.dispatch-answer self answer parsed-answer head id seq))))))

  (defn sender [self]
    (for [i (range self.send-attempts)]
      (for [#(seq fp) (enumerate self.fps)]
        (unless fp.answers
          (.info self.logger "[send] turn=%d, seq=%d, name=%s" i seq fp.__class__.__name__)
          (for [probe fp.probes]
            (.send-probe self probe)
            (sleep self.send-interval))))
      (sleep self.send-timewait)
      (.dispatch-answers self)
      (let [count (cfor sum fp self.fps (not fp.answers))]
        (.info self.logger "[send] turn=%d, unanswered=%d/%d" i count (len self.fps))
        (when (= count 0)
          (break)))))

  (defn recver [self]
    (while (not self.send-finished)
      (let [#(rlist _ _) (select [self.pcap.fd] (list) (list) 0.1)]
        (when rlist
          (.recv-answers self)))))

  (defn run [self]
    (for [fp self.fps]
      (.prepare fp))
    (.prepare self)
    (let [recver (Thread :target self.recver)]
      (.start recver)
      (try
        (.sender self)
        (except [e Exception]
          (.info self.logger "[send]: except while sending %s" e))
        (finally
          (setv self.send-finished True)
          (.join recver))))
    (.cleanup self)))

(defclass FP []
  (defn #-- init [self ctx seq]
    (setv self.ctx ctx
          self.seq seq))

  (defn [cached-property] idseqB [self]
    (idseq-packB self.ctx.id self.seq))

  (defn [cached-property] idseqH [self]
    (idseq-packH self.ctx.id self.seq))

  (defn prepare [self]
    (setv self.parsed-probes  (.make-probes self)
          self.probes         (lfor probe self.parsed-probes (.build probe))
          self.parsed-answers (list)
          self.answers        (list)))

  (defn validate [self head]
    True)

  (defn make-probe [self]
    (raise NotImplementedError))

  (defn make-probes [self]
    [(.make-probe self)])

  (defn make-ipv6 [self #** kwargs]
    (IPv6 :fl self.idseqB :src self.ctx.src :dst self.ctx.dst #** kwargs))

  (defn make-ipv6-with-ether [self #** kwargs]
    (/ (Ether :src self.ctx.mac-src :dst self.ctx.mac-dst)
       (.make-ipv6 self #** kwargs)))

  (defn make-frag [self #** kwargs]
    (IPv6Frag :id self.idseqB #** kwargs))

  (defn make-echo-req [self [code 0] [data (bytes 32)]]
    (/ (ICMPv6 :type ICMPv6Type.EchoReq :code code)
       (ICMPv6EchoReq :id self.ctx.id :seq self.seq)
       data))

  (defn make-udp [self]
    (UDP :src self.idseqB :dst self.idseqB))

  (defn make-tcp [self #** kwargs]
    (TCP :src self.idseqB :dst self.idseqB :seq self.idseqH #** kwargs))

  (defn build-payload [self payload #** kwargs]
    (let [packet (/ (.make-ipv6 self #** kwargs) payload)]
      (.build packet)
      packet.pload))

  (defn build-echo-req [self [code 0] [data (bytes 32)] #** kwargs]
    (.build-payload self (.make-echo-req self code data) #** kwargs)))

(defclass ICMPv6FP [FP]
  (defn validate [self head]
    (isinstance head ICMPv6)))

(defclass TCPFP [FP]
  (defn validate [self head]
    (isinstance head TCP)))

(defclass [fp-register] ExtUnk [ICMPv6FP]
  (defn make-probe [self]
    (/ (.make-ipv6-with-ether self :nh 150)
       (bytes 32))))

(defclass _ExtFP [ICMPv6FP]
  (defn make-ext [self]
    (raise NotImplementedError))

  (defn make-probe [self]
    (/ (.make-ipv6-with-ether self)
       (.make-ext self)
       (.make-echo-req self))))

(defclass _ExtDupFP [_ExtFP]
  (setv n None)

  (defn make-ext [self]
    (if (= self.n 1)
        (IPv6DestOpts)
        (/ #* (gfor _ (range self.n) (IPv6DestOpts))))))

(defclass [fp-register] ExtDup1   [_ExtDupFP] (setv n   1))
(defclass [fp-register] ExtDup2   [_ExtDupFP] (setv n   2))
(defclass [fp-register] ExtDup8   [_ExtDupFP] (setv n   8))
(defclass [fp-register] ExtDup32  [_ExtDupFP] (setv n  32))
(defclass [fp-register] ExtDup128 [_ExtDupFP] (setv n 128))

(defclass [fp-register] ExtOrd1 [_ExtFP]
  (defn make-ext [self]
    (IPv6HBHOpts)))

(defclass [fp-register] ExtOrd2 [_ExtFP]
  (defn make-ext [self]
    (/ (IPv6DestOpts) (IPv6HBHOpts))))

(defclass [fp-register] ExtOrd3 [_ExtFP]
  (defn make-ext [self]
    (/ (IPv6HBHOpts) (IPv6DestOpts) (IPv6HBHOpts))))

(defclass _OptFP [_ExtFP]
  (defn make-opt [self]
    (raise NotImplementedError))

  (defn make-opts [self]
    [(.make-opt self)])

  (defn make-ext [self]
    (IPv6DestOpts :opts (.make-opts self))))

(defclass _OptUnkFP [_OptFP]
  (setv type None)

  (defn make-opt [self]
    #((+ (<< self.type 6) 0x37) (bytes 4))))

(defclass [fp-register] OptUnk00 [_OptUnkFP] (setv type 0))
(defclass [fp-register] OptUnk01 [_OptUnkFP] (setv type 1))
(defclass [fp-register] OptUnk10 [_OptUnkFP] (setv type 2))
(defclass [fp-register] OptUnk11 [_OptUnkFP] (setv type 3))

(defclass [fp-register] OptPadF [_OptFP]
  (defn make-opt [self]
    #(IPv6Opt.PadN b"\xff\xff\xff\xff")))

(defclass _OptPadOFP [_OptFP]
  (setv n None)

  (defn make-opts [self]
    (lfor _ (range self.n) #(IPv6Opt.Pad1 b""))))

(defclass [fp-register] OptPadO2    [_OptPadOFP] (setv n    2))
(defclass [fp-register] OptPadO4    [_OptPadOFP] (setv n    4))
(defclass [fp-register] OptPadO6    [_OptPadOFP] (setv n    6))
(defclass [fp-register] OptPadO8    [_OptPadOFP] (setv n    8))
(defclass [fp-register] OptPadO32   [_OptPadOFP] (setv n   32))
(defclass [fp-register] OptPadO128  [_OptPadOFP] (setv n  128))
(defclass [fp-register] OptPadO1024 [_OptPadOFP] (setv n 1024))

(defclass _OptPadTFP [_OptFP]
  (setv n None)

  (defn make-opts [self]
    (lfor _ (range (>> self.n 1)) #(IPv6Opt.PadN 2))))

(defclass [fp-register] OptPadT2    [_OptPadTFP] (setv n    2))
(defclass [fp-register] OptPadT4    [_OptPadTFP] (setv n    4))
(defclass [fp-register] OptPadT6    [_OptPadTFP] (setv n    6))
(defclass [fp-register] OptPadT8    [_OptPadTFP] (setv n    8))
(defclass [fp-register] OptPadT32   [_OptPadTFP] (setv n   32))
(defclass [fp-register] OptPadT128  [_OptPadTFP] (setv n  128))
(defclass [fp-register] OptPadT1024 [_OptPadTFP] (setv n 1024))

(defclass _OptPadNFP [_OptFP]
  (setv n None)

  (defn make-opt [self]
    #(IPv6Opt.PadN self.n)))

(defclass [fp-register] OptPadN2   [_OptPadNFP] (setv n   2))
(defclass [fp-register] OptPadN4   [_OptPadNFP] (setv n   4))
(defclass [fp-register] OptPadN6   [_OptPadNFP] (setv n   6))
(defclass [fp-register] OptPadN8   [_OptPadNFP] (setv n   8))
(defclass [fp-register] OptPadN32  [_OptPadNFP] (setv n  32))
(defclass [fp-register] OptPadN128 [_OptPadNFP] (setv n 128))

(defclass _OptPadUTFP [_OptFP]
  (setv n None)

  (defn make-opts [self]
    (lfor _ (range (>> self.n 1)) #(0x37 b""))))

(defclass [fp-register] OptPadUT2    [_OptPadUTFP] (setv n    2))
(defclass [fp-register] OptPadUT4    [_OptPadUTFP] (setv n    4))
(defclass [fp-register] OptPadUT6    [_OptPadUTFP] (setv n    6))
(defclass [fp-register] OptPadUT8    [_OptPadUTFP] (setv n    8))
(defclass [fp-register] OptPadUT32   [_OptPadUTFP] (setv n   32))
(defclass [fp-register] OptPadUT128  [_OptPadUTFP] (setv n  128))
(defclass [fp-register] OptPadUT1024 [_OptPadUTFP] (setv n 1024))

(defclass _OptPadUNFP [_OptFP]
  (setv n None)

  (defn make-opt [self]
    #(0x37 (bytes (- self.n 2)))))

(defclass [fp-register] OptPadUN2   [_OptPadUNFP] (setv n   2))
(defclass [fp-register] OptPadUN4   [_OptPadUNFP] (setv n   4))
(defclass [fp-register] OptPadUN6   [_OptPadUNFP] (setv n   6))
(defclass [fp-register] OptPadUN8   [_OptPadUNFP] (setv n   8))
(defclass [fp-register] OptPadUN32  [_OptPadUNFP] (setv n  32))
(defclass [fp-register] OptPadUN128 [_OptPadUNFP] (setv n 128))

(defclass [fp-register] FragDup1 [_ExtFP]
  (defn make-ext [self]
    (.make-frag self)))

(defclass [fp-register] FragDup2 [_ExtFP]
  (defn make-ext [self]
    (/ (.make-frag self)
       (IPv6Frag :id (<< self.seq 2)))))

(defclass [fp-register] FragOrd1 [_ExtFP]
  (defn make-ext [self]
    (/ (.make-frag self)
       (IPv6DestOpts))))

(defclass [fp-register] FragOrd2 [_ExtFP]
  (defn make-ext [self]
    (/ (IPv6DestOpts)
       (.make-frag self))))

(defclass [fp-register] FragOrd3 [_ExtFP]
  (defn make-ext [self]
    (/ (.make-frag self)
       (IPv6HBHOpts))))

(defclass [fp-register] FragRes1 [_ExtFP]
  (defn make-ext [self]
    (.make-frag self :res1 1)))

(defclass [fp-register] FragRes2 [_ExtFP]
  (defn make-ext [self]
    (.make-frag self :res2 1)))

(defclass _Frag2FP [ICMPv6FP]
  (defn make-frag-2 [self data1 data2 [nh IPProto.ICMPv6] [nh1 None] [nh2 None] [offset None]]
    (when (is nh1 None) (setv nh1 nh))
    (when (is nh2 None) (setv nh2 nh))
    (when (is offset None)
      (let [#(div mod) (divmod (len data1) 8)]
        (unless (= mod 0)
          (raise RuntimeError))
        (setv offset div)))
    [(/ (.make-ipv6-with-ether self) (.make-frag self :nh nh1 :M 1) data1)
     (/ (.make-ipv6-with-ether self) (.make-frag self :nh nh2 :offset offset) data2)]))

(defclass [fp-register] FragHdr1 [_Frag2FP]
  (defn make-probes [self]
    (let [data (.build-echo-req self)]
      (.make-frag-2 self (cut data 8) (cut data 8 None) :nh1 IPProto.ICMPv6 :nh2 IPProto.ICMPv4))))

(defclass [fp-register] FragHdr2 [FragHdr1]
  (defn make-probes [self]
    (reversed (#super make-probes))))

(defclass [fp-register] FragHdr3 [_Frag2FP]
  (defn make-probes [self]
    (let [data1 (.build (IPv6DestOpts :nh IPProto.ICMPv6))
          data2 (.build-echo-req self)]
      (.make-frag-2 self data1 data2 :nh IPProto.DestOpts))))

(defclass [fp-register] FragLen0 [_Frag2FP]
  (defn make-probes [self]
    (let [data (.build-echo-req self)]
      (.make-frag-2 self data b""))))

(defclass [fp-register] FragLen12 [_Frag2FP]
  (defn make-probes [self]
    (let [data (.build-echo-req self)]
      (.make-frag-2 self (cut data 12) (cut data 8 None) :offset 1))))

(defclass [fp-register] FragLen20 [_Frag2FP]
  (defn make-probes [self]
    (let [data (.build-echo-req self)]
      (.make-frag-2 self (cut data 20) (cut data 16 None) :offset 2))))

(defclass [fp-register] FragOwt1 [_Frag2FP]
  (defn make-probes [self]
    (let [data (.build-echo-req self)]
      (.make-frag-2 self (cut data 16) (cut data 8 None) :offset 1))))

(defclass [fp-register] FragOwt2 [_Frag2FP]
  (defn make-probes [self]
    (let [data (.build-echo-req self)
          data1 (+ (cut data 8) b"\xff\xff\xff\xff\xff\xff\xff\xff")
          data2 (cut data 8 None)]
      (.make-frag-2 self data1 data2 :offset 1))))

(defclass [fp-register] FragOwt3 [FragOwt2]
  (defn make-probes [self]
    (reversed (#super make-probes))))

(defclass [fp-register] FragOwt4 [_Frag2FP]
  (defn make-probes [self]
    (let [data (.build-echo-req self)
          data1 (cut data 16)
          data2 (+ b"\xff\xff\xff\xff\xff\xff\xff\xff" (cut data 16))]
      (.make-frag-2 self data1 data2 :offset 1))))

(defclass [fp-register] FragOwt5 [FragOwt4]
  (defn make-probes [self]
    (reversed (#super make-probes))))

(defclass [fp-register] EchoCode [ICMPv6FP]
  (defn make-probe [self]
    (/ (.make-ipv6-with-ether self)
       (.make-echo-req self :code 1))))

(defclass [fp-register] UDPPort [ICMPv6FP]
  (defn make-probe [self]
    (/ (.make-ipv6-with-ether self)
       (.make-udp self)
       (bytes 32))))

(defclass [fp-register] TCP1 [TCPFP]
  (defn make-probe [self]
    (/ (.make-ipv6-with-ether self)
       (.make-tcp self))))

(defclass [fp-register] TCP2 [TCPFP]
  (defn make-probe [self]
    (/ (.make-ipv6-with-ether self)
       (.make-tcp self :S 1))))

(defclass [fp-register] TCP3 [TCPFP]
  (defn make-probe [self]
    (/ (.make-ipv6-with-ether self)
       (.make-tcp self :A 1))))

(defclass [fp-register] TCP4 [TCPFP]
  (defn make-probe [self]
    (/ (.make-ipv6-with-ether self)
       (.make-tcp self :F 1 :P 1 :U 1))))

(defmain []
  (let [args (parse-args [["-i" "--iface"]
                          ["-d" "--dst"]
                          ["-s" "--src"]
                          ["-n" "--next-hop"]
                          ["-D" "--mac-dst"]
                          ["-S" "--mac-src"]
                          ["-A" "--send-attempts" :type int :default 2]
                          ["-I" "--send-interval" :type float :default 0.01]
                          ["-T" "--send-timewait" :type float :default 0.2]
                          ["-o" "--dump-path" :default "fp6"]
                          ["-l" "--list" :action "store_true" :default False]])]
    (let [ctx (FPCtx args.dst
                     :iface args.iface :src args.src :next-hop args.next-hop :mac-dst args.mac-dst :mac-src args.mac-src
                     :send-attempts args.send-attempts :send-interval args.send-interval :send-timewait args.send-timewait
                     :dump-path args.dump-path)]
      (logging.basicConfig
        :level   "INFO"
        :format  "%(asctime)s %(name)s %(levelname)s %(message)s"
        :datefmt "%H:%M:%S")
      (.log-info ctx)
      (unless args.list
        (.run ctx)))))
