(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (str.to.re "a"))
(assert (str.in.re key (QuoteRegex (re.* (re.++ (str.to.re """") (re.union (str.to.re "z") aRegex))))))
(assert (= 1 (str.len key)))
(check-sat)
(get-model)
