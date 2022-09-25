(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) (str.len Username)))
(assert (> 64 0))
(assert (<= (str.len Domainname) 256))
(assert (> (str.len Domainname) 0))
(assert (= Email (str.++ "z" "@")))
(assert (str.in.re Email (re.++ (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.+ (re.++ (re.++ (str.to.re "@") (re.++ (re.+ (re.+ (re.union (re.range "A" "Z") (re.union (re.range "0" "9") (re.range "a" (str.++ Username Domainname)))))) (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.+ (str.to.re "."))))) (re.range "A" "Z")))) (re.range "A" "Z"))))
(assert (not (str.in.re Domainname (re.++ re.allchar (re.* (str.to.re "."))))))
(check-sat)
