(declare-const key String)
(declare-const val String)
(assert (str.in.re key (re.* (re.range "a" "b"))))
(assert (<= (str.len key) (str.len key)))
(assert (>= 14 10))
(check-sat)
(get-model)
