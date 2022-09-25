(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (re.++ (str.to.re """""") (re.++ aRegex (str.to.re """"""))))
(assert (str.in.re key (QuoteRegex (str.to.re "aa"))))
(assert (= 4 (str.len key)))
(check-sat)
(get-model)
