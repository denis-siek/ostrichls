(declare-const key String)
(declare-const val String)
(assert (str.in.re key (re.* (re.range "a" "b"))))
(assert (<= (str.to.int key) (str.len key)))
(assert (>= 27 3))
(check-sat)
(get-model)
