(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.* (str.to.re "ay"))))
(assert (= (str.to.int x) 0))
(assert (not (= x "ab|T'&[")))
(assert (not (= x "C]8~bsbjN")))
(assert (not (= x "3Xo=S' 'V:LaxBr;\\T")))
(assert (not (= x "bbb:Yb")))
(assert (not (= x "bb>P`*jQq""o")))
(assert (not (= x "xV_a'\x0c'&@fbyOF`")))
(assert (not (= x "DQEBa")))
(check-sat)
(get-model)
