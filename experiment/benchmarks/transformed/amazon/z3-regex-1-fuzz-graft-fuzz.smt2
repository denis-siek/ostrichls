(declare-const S String)
(assert (not (str.in.re S (re.++ (str.to.re "aB`7(~'\x0b'5o>^FnTMD'\x0b'FPM:'''\t':.f#51EP';4U66rc|TL'7SwOCcL`KWVRqtwsB!08lm~' '1n") re.allchar))))
(assert (str.in.re S (re.++ (re.union (str.to.re "`}TN'\t'e/(") (re.++ (str.to.re "9") re.allchar)) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)
