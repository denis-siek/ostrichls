(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (re.++ (re.union (str.to.re "f") aRegex) (str.to.re "u")))
(assert (str.in.re key (QuoteRegex (re.* (str.to.re "")))))
(assert (= (str.len key) 1))
(check-sat)
(get-model)
