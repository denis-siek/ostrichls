(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "\\2xcskG'M5'MM"))))
(assert (str.in.re x (re.+ (str.to.re "VV[+w(Zm''\t''ev''\x0b''HaAvv*4''\x0c''oomxb'5ou'<UOG&PP>[,}_2b@f()''\x0b''z0?PEP=XxI!|/K<69IrXH3lH:""-7AiM7v;x4Ih^;)x""yiYyHP3`~V`qSF!5%Et)Z5kvHQ;='J''\x0b''`RB?:''\x0c''J+wa+fx}]pl})v@0''\t''r"))))
(assert (> (str.to.int x) 11))
(assert (< (str.len x) 9))
(check-sat)
(get-model)
