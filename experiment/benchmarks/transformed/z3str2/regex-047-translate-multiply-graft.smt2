(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (str.to.re "BB"))
(assert (str.in.re key (QuoteRegex (re.* (re.++ (re.++ (str.to.re "yy") aRegex) (str.to.re "yy"))))))
(assert (= 4 (str.len key)))
(check-sat)
(get-model)
