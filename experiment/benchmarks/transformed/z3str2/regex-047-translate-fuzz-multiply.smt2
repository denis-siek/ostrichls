(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (re.union (re.++ (str.to.re "yy") aRegex) (str.to.re "")))
(assert (str.in.re key (QuoteRegex (re.+ (str.to.re "BB")))))
(assert (= (str.len key) 4))
(check-sat)
(get-model)
