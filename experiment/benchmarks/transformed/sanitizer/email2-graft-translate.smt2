(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) (str.len Username)))
(assert (> 64 0))
(assert (<= (str.len Domainname) 256))
(assert (> (str.len Domainname) 0))
(assert (= Email "0"))
(assert (str.in.re Email (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.++ (str.to.re "`") (re.++ (re.+ (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (str.to.re "K"))) (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range (str.++ Username (str.++ "`" Domainname)) "9")))))))))
(assert (not (str.in.re Domainname (re.++ (re.* re.allchar) (re.++ (re.* re.allchar) (str.to.re "K"))))))
(check-sat)
