(declare-const key String)
(declare-const val String)
(assert (str.in.re key (re.+ (re.range "a" "b"))))
(assert (<= 3 (str.len key)))
(assert (>= 27 (str.to.int key)))
(check-sat)
(get-model)
