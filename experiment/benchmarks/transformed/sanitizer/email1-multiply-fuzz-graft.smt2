(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= 0 147))
(assert (> (str.to.int Username) 0))
(assert (<= (str.to.int Domainname) 188))
(assert (> (str.to.int Domainname) (str.to.int Username)))
(assert (= Email (str.++ Username "9")))
(assert (str.in.re Email (re.union (re.* (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.++ (str.to.re "D`M") (re.++ (re.+ (re.union (re.+ (re.++ (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))) (str.to.re "r."))) (re.* (re.++ (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))))))))
(assert (str.in.re Domainname (re.++ (re.++ (re.union (str.to.re "2C5") (re.range "0" "5")) (re.++ (re.union (str.to.re "2?") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "0'' ''|") (str.to.re "1n"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "Q") (re.++ (re.++ (re.++ (str.to.re "D''\n''v2crce") (re.range "0" "5")) (re.++ (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "0") (str.to.re "c\\!B"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re ".\\") (re.++ (re.union (re.++ (str.to.re "=aW''\t''") (re.range "0" "5")) (re.union (re.++ (str.to.re "22") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "") (str.to.re "6IB`"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "CQ.") (re.++ (re.++ (str.to.re "2") (re.range "0" "5")) (re.++ (re.++ (str.to.re "_''\x0c''") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.union (str.to.re """g") (re.range "0" (str.++ "@" Domainname)))) (re.union (re.range "0" "9") (re.opt (str.to.re "s3W"))))))))))))))
(check-sat)
