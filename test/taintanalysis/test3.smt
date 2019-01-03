(declare-rel invTaint (Int Bool Bool))
(declare-rel error_taint_0_taint_24_initial_23_x ())
(declare-rel error_taint_2_taint_26_initial_25_y ())
(declare-rel error1 ())
(declare-var A Bool)
(declare-var B Bool)
(declare-var C Bool)
(declare-var D Bool)
(declare-var step1 Int)
(declare-var step2 Int)

(rule (! (=> (and B A (= step1 0)) (invTaint step1 B A)) :named initTaintRule))
(rule (! (=> (and (= A C) (ite (= step2 10) B (not B)) (= step2 (+ step1 1)) (invTaint step1 D C)) (invTaint step2 B A)) :named nextTaintRule))
(rule (! (=> (and B (> step1 0) (invTaint step1 B A)) error_taint_0_taint_24_initial_23_x) :named error_rule_taint_1_taint_24_initial_23_x))
(rule (! (=> (and (not A) (invTaint step1 B A)) error_taint_2_taint_26_initial_25_y) :named error_rule_taint_3_taint_26_initial_25_y))


(query error_taint_2_taint_26_initial_25_y :print-certificate true)
(query error_taint_0_taint_24_initial_23_x :print-certificate true)
