(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.* (re.++ (str.to.re "") (str.to.re "")))))
(assert (= 12 (str.to.int x)))
(assert (not (= x "++]]")))
(assert (not (= x "DD::KK__@@JJii")))
(assert (not (= x "]]]]")))
(assert (not (= x "hh")))
(assert (not (= x "ZZ'''\r''\r''';;ss")))
(assert (not (= x "JJnnee")))
(assert (not (= x ";;99NN++")))
(check-sat)
(get-model)
