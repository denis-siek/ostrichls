(declare-const x String)
(assert (= x "aaaaaaaabbbbbbbbccccccccddddddddccccccccddddddddeeeeeeee"))
(assert (str.in.re x (re.union (re.* (str.to.re "aaaaaaaabbbbbbbbccccccccdddddddd")) (re.* (str.to.re "ccccccccddddddddeeeeeeee")))))
(check-sat)
(get-model)
