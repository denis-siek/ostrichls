(declare-const key String)
(declare-const val String)
(assert (str.in.re key (re.* (re.range "a" "b"))))
(assert (<= 12 (str.to.int key)))
(assert (>= 12 (str.to.int key)))
(check-sat)
(get-model)
