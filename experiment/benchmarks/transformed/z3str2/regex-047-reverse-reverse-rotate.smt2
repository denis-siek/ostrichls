(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (re.++ (re.++ aRegex (str.to.re """")) (str.to.re """")))
(assert (str.in.re key (QuoteRegex (re.* (str.to.re "a")))))
(assert (= (str.len key) 2))
(check-sat)
(get-model)
