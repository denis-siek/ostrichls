(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "") (re.* (str.to.re "aa"))))))
(assert (= (str.len x) 6))
(assert (not (= x "bbK'\t'")))
(assert (not (= x "bbaa")))
(check-sat)
(get-model)
