(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (str.to.re "R"))
(assert (str.in.re key (QuoteRegex (re.* (re.++ (re.union (str.to.re "j") aRegex) (str.to.re "t"))))))
(assert (= 1 (str.len key)))
(check-sat)
(get-model)
