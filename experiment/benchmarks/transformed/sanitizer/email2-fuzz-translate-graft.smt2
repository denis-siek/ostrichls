(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 24))
(assert (> (str.to.int Username) 0))
(assert (<= (str.len Domainname) 88))
(assert (> 0 (str.len Domainname)))
(assert (= Email (str.++ Username "9")))
(assert (str.in.re Email (re.union (re.* (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.++ (str.to.re "I") (re.++ (re.+ (re.union (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.union (str.to.re "{") (re.* re.allchar)))) (re.* (re.++ (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" (str.++ "I" Domainname))))))))))
(assert (not (str.in.re Domainname (re.++ (re.* re.allchar) (str.to.re "")))))
(check-sat)
