(declare-const x String)
(assert (= x "ccccddddeeeeaaaabbbbccccddddccccddddeeee"))
(assert (str.in.re x (re.* (re.union (str.to.re "aaaabbbbccccdddd") (str.to.re "ccccddddeeee")))))
(check-sat)
(get-model)
