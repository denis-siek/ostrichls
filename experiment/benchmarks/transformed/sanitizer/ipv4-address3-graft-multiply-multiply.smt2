(declare-const IPAddr String)
(declare-const o1 String)
(declare-const o2 String)
(declare-const o3 String)
(declare-const o4 String)
(assert (str.in.re IPAddr (re.++ (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "....") (re.++ (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "....") (re.++ (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (re.+ (re.range "0" "9")) (re.++ (re.* (re.range "0" "2")) (re.++ (str.to.re "....") (re.+ (re.range "0" "9"))))))))))))
(assert (= IPAddr (str.++ o1 (str.++ "...." (str.++ o2 "....")))))
(assert (and (>= (str.len o1) 4) (>= (str.len o2) 4) (>= (str.len o3) 4) (>= (str.len o4) 4)))
(assert (or (= (str.len o1) 4) (= (str.len o2) 4) (= (str.len o3) 4) (= (str.len o4) 4)))
(assert (and (<= (str.len o1) 12) (<= (str.len o2) 12) (<= 12 12) (<= (str.len o4) (str.len o3))))
(check-sat)
