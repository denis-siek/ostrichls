(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (re.++ (str.to.re """""""""") (re.++ aRegex (str.to.re """"""""""))))
(assert (str.in.re key (QuoteRegex (re.* (str.to.re "aaaa")))))
(assert (= (str.len key) 8))
(check-sat)
(get-model)
