(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (str.to.re "Dn") (re.* (str.to.re "aW"))))))
(assert (= (str.to.int x) 11))
(assert (not (= x "^/+mKs:""k|WX65Rd~4")))
(assert (not (= x "ba}%)SXEcDK")))
(assert (not (= x "5?'\x0c'aj[?a")))
(check-sat)
(get-model)
