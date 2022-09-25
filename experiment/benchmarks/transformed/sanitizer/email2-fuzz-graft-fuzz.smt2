(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) (str.to.int Domainname)))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) 259))
(assert (> 19 0))
(assert (= Email (str.++ Username "a")))
(assert (str.in.re Email (re.++ (re.+ (re.++ (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.union (str.to.re "k") (re.++ (re.* (re.++ (re.+ (re.++ (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))) (str.to.re "7"))) (re.* (re.++ (re.range (str.++ "" Domainname) "z") (re.union (re.range "A" "Z") (re.range "0" "9")))))))))
(assert (not (str.in.re Domainname (re.union (re.+ re.allchar) (re.union (re.* re.allchar) (str.to.re "_"))))))
(check-sat)
