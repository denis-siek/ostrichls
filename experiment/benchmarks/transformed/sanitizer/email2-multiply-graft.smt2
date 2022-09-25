(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 128))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) 512))
(assert (> 0 (str.len Domainname)))
(assert (= Email (str.++ Username "0")))
(assert (str.in.re Email (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.++ (str.to.re "@@") (re.++ (re.+ (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (str.to.re ".."))) (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range (str.++ "@@" Domainname) "9")))))))))
(assert (not (str.in.re Domainname (re.++ (re.* re.allchar) (re.++ (re.* re.allchar) (str.to.re ".."))))))
(check-sat)
