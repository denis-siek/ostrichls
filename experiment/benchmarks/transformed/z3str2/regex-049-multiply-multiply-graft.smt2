(declare-const key String)
(declare-const val String)
(assert (str.in.re key (re.* (re.range "a" "b"))))
(assert (<= (str.len key) 20))
(assert (>= 28 (str.len key)))
(check-sat)
(get-model)
