(declare-const IPAddr String)
(declare-const o1 String)
(declare-const o2 String)
(declare-const o3 String)
(declare-const o4 String)
(assert (str.in.re IPAddr (re.++ (re.union (re.* (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.union (str.to.re ".") (re.union (re.union (re.+ (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.union (str.to.re "") (re.++ (re.union (re.+ (re.range "0" "2")) (re.union (re.+ (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.union (str.to.re ".") (re.union (re.+ (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.* (re.range "0" "9"))))))))))))
(assert (= IPAddr (str.++ o1 (str.++ "" (str.++ o2 (str.++ "X" (str.++ o3 (str.++ "!'\x0b'" o4))))))))
(assert (and (>= (str.to.int o1) 1) (>= (str.to.int o2) 2) (>= (str.to.int o3) 2) (>= (str.to.int o4) 0)))
(assert (or (= (str.to.int o1) 0) (= (str.len o2) 1) (= (str.len o3) 8) (= (str.len o4) 6)))
(assert (and (<= (str.len o1) 0) (<= (str.len o2) 0) (<= (str.len o3) 1) (<= (str.len o4) 6)))
(check-sat)
