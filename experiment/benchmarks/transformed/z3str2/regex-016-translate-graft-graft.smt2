(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "`Q|R")))
(assert (= 11 (str.len x)))
(assert (not (= x "`Q|R123`Q|R")))
(assert (not (= x "`Q|R`Q|R123")))
(check-sat)
(get-model)
