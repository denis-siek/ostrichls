(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 64))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) 256))
(assert (> (str.len Domainname) 0))
(assert (= Email "9"))
(assert (str.in.re Email (re.++ (re.++ (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" (str.++ "9" Username))))) (re.+ (re.++ (re.++ (re.* re.allchar) (str.to.re ".")) (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9"))))))) (str.to.re "@")) (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (str.to.re ".")))))))
(assert (not (str.in.re Domainname (re.++ (re.range "0" (str.++ Domainname "@")) (re.* re.allchar)))))
(check-sat)
