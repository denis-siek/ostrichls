(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.to.int Username) 11))
(assert (> (str.len Username) 0))
(assert (<= (str.to.int Domainname) 46))
(assert (> (str.to.int Domainname) 0))
(assert (= Email (str.++ (str.++ Domainname "") Username)))
(assert (str.in.re Email (re.union (re.union (re.union (re.* (re.++ (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.+ (re.++ (str.to.re "E") (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9"))))))) (str.to.re "S")) (re.+ (re.union (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))))))
(assert (not (str.in.re Domainname (re.++ (re.++ (re.+ re.allchar) (str.to.re "_")) (re.+ re.allchar)))))
(check-sat)
