(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ y x) (str.++ n m)))
(assert (str.in.re n (re.+ (str.to.re "ccTTyy"))))
(assert (= (str.to.int x) (str.to.int m)))
(check-sat)
(get-model)
