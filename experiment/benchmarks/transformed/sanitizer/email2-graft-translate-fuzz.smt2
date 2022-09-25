(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) (str.len Username)))
(assert (> 30 0))
(assert (<= (str.len Domainname) 26))
(assert (> (str.len Domainname) 0))
(assert (= Email ";"))
(assert (str.in.re Email (re.++ (re.+ (re.++ (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.++ (str.to.re "`") (re.union (re.+ (re.union (re.* (re.++ (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))) (str.to.re "K"))) (re.* (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range (str.++ Username (str.++ "`" Domainname)) "9")))))))))
(assert (not (str.in.re Domainname (re.union (re.+ re.allchar) (re.++ (re.* re.allchar) (str.to.re "R"))))))
(check-sat)
