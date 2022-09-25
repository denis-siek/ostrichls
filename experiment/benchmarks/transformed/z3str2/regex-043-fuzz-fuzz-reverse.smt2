(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "") (str.to.re "")))))
(assert (= 0 (str.len x)))
(assert (not (= x "}")))
(assert (not (= x "")))
(assert (not (= x "n")))
(assert (not (= x "b")))
(assert (not (= x "aW2;:=,Jxhzqjk>n")))
(assert (not (= x "V")))
(assert (not (= x "aJw")))
(check-sat)
(get-model)
