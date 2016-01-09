;;
;;
;;            LOGOS
;;
;;
;; a program to compute logic symbolically
;;
;; author: Damien Mattei
;;
;; date : 2014 , 2015
;;
;; version 1.8
;;
;; LISP version (tested with Clozure CL, CLisp, CMU Common Lisp,GNU Common Lisp)
;;
;; windows : (load "c:/Users/mattei/Google Drive/info/logos.lisp")
;;
;; apple : (load "/Users/mattei/Google Drive/info/logos.lisp")
;;
;; linux : (load "/home/mattei/Copy/info/logos.lisp") 
;;
;;
;; provides :
;;
;; transformation towards Disjonctive Normal Form
;; transformation towards Conjonctive Normal Form
;; transformation from prefix to infix notation
;; simplification of DNF and CNF
;; search for antilogies and tautologies
;; 
;; example of expression put in DNF:
;;
;; with Clozure  Common LISP:
;;
;;  (pretty-display  (dnf-infix-symb (symb-compute-sum 'Ci 'a 'b))) -> (!A ^ !B ^ CI)  V  (A ^ B ^ CI)  V  (A ^ !B ^ !CI)  V  (!A ^ B ^ !CI) 
;;
;; (cnf-infix-symb '(and (=> (and p q) r) (=> (not (and p q)) r))) -> ((!P V !Q V R) ^ (P V R) ^ (Q V R))
;;
;;
;; (enlight-dnf (symb-compute-sum 'Ci 'a 'b)) -> (A^!B^!CI)V(!A^B^!CI)V(!A^!B^CI)V(A^B^CI)
;;
;; (enlight-dnf '(or (and a b) a)) -> A
;;
;; (enlight-dnf  '(and (=> (and p q) r) (=> (not (and p q)) r))) -> R
;;
;; (dnf-infix-symb (symb-compute-carry T 'b1 'b2)) -> ((B1 ^ B2) V (!B1 ^ B2) V (B1 ^ !B2))
;;
;; (dnf-infix-symb '(and (=> (and p q) r) (=> (not (and p q)) r))) -> ((P ^ Q ^ R) V (!P ^ R) V (!Q ^ R) V R)
;;
; with DrRacket Scheme:
;
; (dnf-infix-symb '(((p . and . q) . => . r) . and . ((not (p . and . q)) . => . r))) -> '((!p ^ r) v (p ^ q ^ r) v (!q ^ r) v r)
;
;
; the same in CNF:
;
; with GNU Common Lisp:
;
; (cnf-infix-symb '(and (=> (and p q) r) (=> (not (and p q)) r))) -> ((P V R) ^ (!P V !Q V R) ^ (Q V R))
; 
;





; Eliminate the logical implications
;
; PHASE1 : on élimine les implications (voir livre "Premier cours de programmation avec Scheme" page 210)
;
; example:
; 
;> (show (elim-implications '(or (=> p q) (not (=> q r)))))
;? (elim-implications '(or (=> p q) (not (=> q r))))
;--> (or (or (not p) q) (not (or (not q) r)))
;
; (elim-implications '(or (=> a b) (not (=> b c)))) -> (OR (OR (NOT A) B) (NOT (OR (NOT B) C)))

(defun elim-implications (expr)
  (cond 
   ((symbol? expr) expr)
   ((boolean? expr) expr)
   ((isNOT? expr) `(not ,(elim-implications (arg expr))))
   ((isIMPLIC? expr) `(or (not ,(elim-implications (arg1 expr))) ,(elim-implications (arg2 expr))))
   (T `(,(operator expr) ,(elim-implications (arg1 expr)) ,(elim-implications (arg2 expr))))))


; Moving in the negation to the leaves of tree
;
; PHASE 2 : on fait rentrer les négations jusqu'aux feuilles de l’arbre
; on ne s’occupe plus des implications !
;
; (move-in-negations '(not (not (not p)))) --> (NOT P)
;
; (move-in-negations '(not (or (not (and a b)) b))) --> (AND (AND A B) (NOT B))

(defun move-in-negations (expr)  
  (cond
   ((or (symbol? expr) ; symbol , ex: 'a
	(boolean? expr)) expr) ; boolean , ex: NIL
   ((and (isNOT? expr) (boolean? (arg expr))) expr)
					; ((and (isNOT? expr) (arg expr)) expr) ; (not T)
					; ((and (isNOT? expr) (not (arg expr))) expr) ; (not NIL)
   ((isNOT? expr) 
    (let 
	((p (arg expr))) ; not (p) 
      (cond
       ((symbol? p) expr)
       ((isNOT? p) (move-in-negations (arg p))) ; (not p)
					; not(a and b) = not(a) or not(b)
       ((isAND? p)
	(let
	    ((a (arg1 p))
	     (b (arg2 p)))
	  `(or ,(move-in-negations `(not ,a)) ,(move-in-negations `(not ,b)))))
					; not(a or b) = not(a) and not(b)
       ((isOR? p) 
	(let
	    ((a (arg1 p))
	     (b (arg2 p)))
	  `(and ,(move-in-negations `(not ,a)) ,(move-in-negations `(not ,b)))))
	(T (error  "Bad syntax (inner)")))))

   ((isOR-AND? expr) ; (op p q)
    (let
	((op (operator expr))
	 (p (arg1 expr))
	 (q (arg2 expr)))
      `(,op ,(move-in-negations p) ,(move-in-negations q))))
    (T (error  "Bad syntax"))))


(defun distribute-and-over-or (expr1 expr2)    ; expr1 et expr2 sont les arguments d'un 'and : ('and expr1 expr2)
  ; remember we have (expr1 and expr2) to distribute over the "or"
  (cond ((isOR? expr1)               ; (expr1 expr2) <--> ( ('or p q) r )
	 (let ((p (arg1 expr1))
	       (q (arg2 expr1))
	       (r expr2))
	   `(or ,(distribute-and-over-or p r) ,(distribute-and-over-or q r)))) ; (p or q) and r = (p and r) or (q and r)
	((isOR? expr2) ;  (expr1 expr2) <--> ( p ('or q r) )
	 (let ((p expr1)
	       (q (arg1 expr2))
	       (r (arg2 expr2)))
	   `(or ,(distribute-and-over-or p q) ,(distribute-and-over-or p r)))) ; p and (q or r) = (p and q) or (p and r)
	(T `(and ,expr1 ,expr2)))) ; else we create the expression ('and expr1 expr2) 


; we make the 'or going out by distributing them over the 'and
;
; PHASE 3 : on fait au contraire sortir les 'or en distribuant les 'and
; on ne s'occupe plus des négations !

(defun phase3-dnf (expr)
  (cond
   ((isOR? expr)
    (let ((p (arg1 expr))
	  (q (arg2 expr)))
      `(or ,(phase3-dnf p) ,(phase3-dnf q))))
   ((isAND? expr)
    (let ((p (arg1 expr))
	  (q (arg2 expr)))
      (distribute-and-over-or (phase3-dnf p) (phase3-dnf q))))
   (T expr))) ; else we leave it unchanged (could be atom, not(x),... )


;(defun rest (lst)
;  (cdr lst))


;(defun first (lst)
;  (car lst))

;; (defun second (lst)
;;   (first (rest lst)))

(defun isOR? (expr)
  (and (consp expr) (equal (car expr) 'or)))

(defun isAND? (expr)
  (and (consp expr) (equal (car expr) 'and)))

; is expression an (OR or AND) ?
(defun isOR-AND? (expr)
  (or (isOR? expr)  (isAND? expr)))

(defun isNOT? (expr)
  (and (consp expr) (equal (car expr) 'not)))

(defun isIMPLIC? (expr)
  (and (consp expr) (equal (car expr) '=>)))

; return the operator of a boolean expression
(defun operator (expr)
  (car expr))

; return the first argument of a binary operation
(defun arg1 (expr)
  (first (rest expr)))

; return the second argument of a binary operation
(defun arg2 (expr)
  (first (rest (rest expr))))

(defun arg (expr)
  (arg1 expr))

; return the arguments of a boolean expression
(defun args (expr)
  (cdr expr))

;(defun pair? (expr)
;  (cond 
;   ((null expr) expr)
;   ((atom expr) NIL)
;  (T (not (end-with-nil? (cdr expr))))))

(defun end-with-nil? (expr)
  (cond 
   ((null expr) T)
   ((atom expr) NIL)
   (T (end-with-nil? (cdr expr)))))

(defun list? (expr)
  (and 
   (listp expr)
   (end-with-nil? (cdr expr))))

(defun boolean? (expr)
  (or (equal expr T) (equal expr NIL)))

(defun symbol? (expr)
  (and (atom expr) (not (null expr))))


;; simplify-negation in a classic recursive way
;; (simplify-negation '(not T)) -> NIL
;; (simplify-negation '(not (not T))) -> T 
(defun simplify-negation (expr)
  (cond
   ((symbol? expr) expr) ;; symbol , ex: 'a
   ((boolean? expr) expr) ;; boolean , ex: NIL
   ((isNOT? expr) ;; (not p)
    (let ((p (simplify-negation (arg1 expr)))) ;; simplify p
      (cond ((equal p T) NIL) ;; !T = NIL
	    ((equal p NIL) T)    ;; !NIL = T
	    (T `(not ,p))))) ;; (not p)
					;; simplify (op p q) 
   ((isOR-AND? expr) `(,(operator expr) ,(simplify-negation (arg1 expr)) ,(simplify-negation (arg2 expr))))))

;;;; simplify expression A ^ F or A ^ T or A v T ....

;; (prefix->infix-symb (simplify (n-arity (simplify-OR (simplify-AND (phase3-dnf (simplify-negation (move-in-negations (elim-implications  (symb-compute-sum  'Cin 'A T)))))))))) -> '((A ^ Cin) v (!A ^ !Cin))
(defun simplify-OR (expr)
  (cond ((symbol? expr) expr) ;; symbol , ex: 'a
	((boolean? expr) expr) ;; boolean , ex: NIL
	((isNOT? expr) `(not ,(simplify-OR (arg expr)))) ;; (not p)
	((isAND? expr) `(and ,(simplify-OR (arg1 expr)) ,(simplify-OR (arg2 expr)))) ;;  and
	((isOR? expr) ;; (or p q)
	 (let ((p-simp (simplify-OR (arg1 expr)))) ;; p simplified
	   (if (equal T p-simp) ;; (or T q)
	       T ;; tautology
	       (let ((q-simp (simplify-OR (arg2 expr)))) ;; q simplified
		 (if (equal T q-simp) ;;  (or p T)
		     T ;; tautology
		     (cond ((equal p-simp NIL) q-simp) ;; (or NIL q)
			   ((equal q-simp NIL) p-simp) ;; (or p NIL)
			   (T `(or ,p-simp ,q-simp)))))))))) ;; (or p q) 


;;;; (prefix->infix-symb (simplify (n-arity (simplify-OR (simplify-AND (phase3-dnf (simplify-negation (move-in-negations (elim-implications  (symb-compute-sum  'Cin 'A T)))))))))) -> '((A ^ Cin) v (!A ^ !Cin))
(defun simplify-AND (expr)
  (cond
   ((symbol? expr) expr) ;; symbol , ex: 'a
   ((boolean? expr) expr) ;; boolean , ex: NIL
   ((isNOT? expr) `(not ,(simplify-AND (arg expr)))) ;; (not p)
   ((isOR? expr) `(or ,(simplify-AND (arg1 expr)) ,(simplify-AND (arg2 expr)))) ;;  or
   ((isAND? expr) ;; (and p q)
    (let ((p-simp (simplify-AND (arg1 expr)))) ;; p simplified
      (if (equal NIL p-simp) ;; (and NIL q)
	  NIL ;; antilogy
	  (let ((q-simp (simplify-AND (arg2 expr)))) ;; q simplified
	    (if (equal NIL q-simp) ;;  (and p NIL)
		NIL ;; antilogy
		(cond
		 ((equal p-simp T) q-simp) ;; (and T q)
		 ((equal q-simp T) p-simp) ;; (and p T)
		 (T `(and ,p-simp ,q-simp)))))))))) ;; (and p q) 


;; (dnf '(not (or (not (and a b)) b)))  --> (AND (AND A B) (NOT B))
(defun dnf (expr)    ;; disjunctive normal form
  ;; (dnf (symb-compute-sum 'Ci 'a 'b))
  ;; -> '(or (or (or (and Ci (and (not a) a)) (and Ci (and (not a) (not b)))) (or (and Ci (and b a)) (and Ci (and b (not b)))))
  ;;   (or (and (not Ci) (and a (not b))) (and (not Ci) (and (not a) b))))
  ;; 
  ;; (dnf (symb-compute-sum  'Cin 'A T))
  ;; -> '(or (or (or (and Cin (and (not A) A)) (and Cin (and (not A) NIL))) (or (and Cin (and T A)) (and Cin (and T NIL)))) (or (and (not Cin) (and A NIL)) (and (not Cin) (and (not A) T))))
  (phase3-dnf (move-in-negations (elim-implications expr))))



;; todo : sort arguments by size 

;; simplify DNF of form ((a ^ b) v a) -> a
;; simplify a prefixed n-arity expression
;;
;;
;; (simplify-DNF-by-unitary-reduction '(or (and a (not b)) (and a b) (and b d) (and a e (not b)) (and a (not b) c)))
;;  -> (or (and b d) (and a b) (and a (not b)))
;;
;; (simplify-DNF-by-unitary-reduction '(or (and a (not b)) (and a b) a (and b d) (and a e (not b)) (and a (not b) c)))
;;  -> (OR (AND B D) A)
;;
;; (simplify-DNF-by-unitary-reduction '(or (a (not b)) (a b) (b d) (a e (not b)) (a (not b) c))) -> (or (b d) (a b) (a (not b)))
;; (simplify-DNF-by-unitary-reduction '(or a (and a (not b)) (and a b) (and b d) (and a e (not b)) (and a (not b) c)))
;;  -> '(or (and b d) a)
;;
;; (simplify-DNF-by-unitary-reduction '(or (and a b) a)) -> 'a
;;
(defun simplify-DNF-by-unitary-reduction (expr)
  (cond
   ((null expr) expr)
   ((is-single-form? expr) expr)
   (T
    (flet ((encaps (expression)  ;; put any remaining element in a set (list)
		   (if (symbol? expression)
		       (list expression)
		     expression))
	   (decaps (expression) ;; extract any element from a list
		   (if (singleton? expression)
		       (first expression)
		     expression)))
	  (let* ((sL (args expr)) ;; extract the arguments of 'or
		 (encaps-args (mapcar #'encaps sL))
		 (reducted-args (parse-args-by-unitary-reduction encaps-args encaps-args)) ;; do unitary reduction
		 (decaps-args (mapcar #'decaps reducted-args)))
	    (if (only-one? decaps-args)
		(first decaps-args)
	      (cons 'or decaps-args))))))) ;; reconstruct 'or expression with simplified arguments list


(defun singleton? (expr)
  (and (list? expr) (symbol? (first expr)) (null (rest expr))))

(defun only-one? (expr)
  (null (rest expr))) 

;; parse-args-by-unitary-reduction = G
;;
;; algo :
;;    
;; (C- means "is element of", !C- means "is not element of ")
;;
;; start with G(sL,sL)
;;
;; G(sL,W) :
;; s C- W  -> G(L,s.F(s,W))
;; s !C- W -> G(L,W)
;; G(0,W)  -> W
;;
;; (parse-args-by-unitary-reduction '((and a (not b)) (and a b) (and b d) (and a e (not b)) (and a (not b) c)) '((and a (not b)) (and a b) (and b d) (and a e (not b)) (and a (not b) c)))
;;   -> '((and b d) (and a b) (and a (not b)))
;;
;; (parse-args-by-unitary-reduction '((and a (not b)) (and a b) (a) (and b d) (and a e (not b)) (and a (not b) c)) '((and a (not b)) (and a b) (a) (and b d) (and a e (not b)) (and a (not b) c))) -> '((and b d) (a))
;;
;;  (parse-args-by-unitary-reduction '((a) (and a (not b)) (and a b) (and b d) (and a e (not b)) (and a (not b) c)) '((a) (and a (not b)) (and a b) (and b d) (and a e (not b)) (and a (not b) c))) -> ((and b d) (a))
;;
;; (parse-args-by-unitary-reduction '((a) (a (not b)) (a b) (b d) (a e (not b)) (a (not b) c)) '((a) (a (not b)) (a b) (b d) (a e (not b)) (a (not b) c))) -> ((B D) (A))
(defun parse-args-by-unitary-reduction (sL W)
  (if (null sL)
      W ;; G(0,W)  -> W
      (let* ((s (first sL))
	     (L (rest sL))
	     (element (member2 s W))) ;; s C-? W
	(if element ;; s C-? W 
	    (let ((F (unitary-reduction s W)))
	      (parse-args-by-unitary-reduction L (cons s F))) ;; s C- W  : G(sL,W) -> G(L,s.F(s,W))
	    (parse-args-by-unitary-reduction L W)))))           ;; s !C- W : G(sL,W) -> G(L,W)


;;;; (define (parse-args-by-unitary-reduction sL W)
;;;;   (if (null? sL)
;;;;       W ;; G(0,W)  -> W
;;;;       (let* ((s (first sL))
;;;; 	    (L (rest sL))
;;;; 	    (element (member s W))) ;; s C-? W
;;;; 	(begin
;;;; 	  (display "s=") (display s) (display "\n")
;;;; 	  (display "W=") (display W) (display "\n")
;;;; 	  (display "element=") (display element) (display "\n")
;;;; 	  (if element ;; s C-? W 
;;;; 	      (let ((F (unitary-reduction s W)))
;;;; 		(begin
;;;; 		  (display "F =") (display F) (display "\n")
;;;; 		  (parse-args-by-unitary-reduction L (cons s F)))) ;; s C- W  : G(sL,W) -> G(L,s.F(s,W))
;;;; 	      (begin
;;;; 		(display "L=") (display L) (display "\n")
;;;; 		(parse-args-by-unitary-reduction L W)))))))           ;; s !C- W : G(sL,W) -> G(L,W)


;; predicate to test the inclusion of a subset in a set
;; (include? '(a) '(a b)) -> T
;; (include? '(a) '(a))  -> T
;; (include? '(a) '((a))) -> NIL ;; <- WARNING
;; (include? '((a)) '((a) (a (not b)) (a b) (b d) (a e (not b)) (a (not b) c))) -> T
;; ? (include? '((b d)) '((a) (a (not b)) (a b) (b d) (a e (not b)) (a (not b) c))) -> T
(defun include? (subset set) ;; (include? cL1 L2)
  (cond
   ((null subset) T) ;; empty subset always include in a set
   ((null set) NIL) ;; if subset is not empty and set is empty then result is false
   (T (and (member2 (first subset) set) (include? (rest subset) set))))) ;; c include in L2 AND L1 include in L2


;; unitary-reduction of sL by k
;; will remove all element of sL containing k
;;
;; (unitary-reduction '(a) '((a b) (b d) (a b c))) -> ((b d))
;; (unitary-reduction '(a (not b)) '((a b) (b d) (a e (not b)) (a (not b) c))) -> ((a b) (b d))
;; (unitary-reduction '(and a (not b)) '((and a b) (and b d) (and a e (not b)) (and a (not b) c))) -> ((and a b) (and b d))
;; (unitary-reduction '(a) '((a b) (b d) (a b c) (a))) -> ((b d))
;; (unitary-reduction '(a) '((a) (a (not b)) (a b) (b d) (a e (not b)) (a (not b) c))) -> ((b d))
;; (unitary-reduction '(z) '((a b) (b d) (a b c))) -> ((a b) (b d) (a b c))
;; 
;; algo:
;; sL = {} -> {}
;; k C s  -> F(k,L)   
;; k !C s -> s.F(k,L)
(defun unitary-reduction (k sL) ;; unitary-reduction = F
  (if (null sL) ;;  sL = 0
      sL
      (let* ((s (first sL))
	    (L (rest sL))
	    (F (unitary-reduction k L)))
	(if (include? k s) ;;       C means "include in", !C means "not include in"
	    F  ;; k C s -> F(k,L)      
	    (cons s F))))) ;; k !C s -> s.F(k,L)


;; (enlight-dnf (symb-compute-sum 'Ci 'a 'b)) -> (a^b^Ci)v(!a^!b^Ci)v(!a^b^!Ci)v(a^!b^!Ci)
;;(defun enlight-dnf (expr)
;;  (compact-display-bracket (prefix->infix-symb (simplify (n-arity (simplify-OR (simplify-AND (simplify-DNF-by-unitary-reduction (dnf expr)))))))))

;; (enlight-dnf (symb-compute-sum 'Ci 'a 'b)) -> (A^B^CI)V(!A^!B^CI)V(!A^B^!CI)V(A^!B^!CI)
;;(define (enlight-dnf expr)
;;  (compact-display-bracket (prefix->infix-symb (simplify-DNF-by-unitary-reduction (simplify (n-arity (simplify-OR (simplify-AND (simplify-DNF-by-unitary-reduction (dnf expr))))))))))

(defun enlight-dnf (expr)
  (compact-display-bracket (prefix->infix-symb (simplify-DNF-by-unitary-reduction (simplify (n-arity (simplify-OR (simplify-AND (simplify-DNF-by-unitary-reduction (dnf expr))))))))))

;; pretty display sans les parentheses de ( expr )
;;=> (pretty-display  (dnf-infix-symb (symb-compute-sum 'Ci 'a 'b)))
;; ->  (!a ^ b ^ !ci)  v  (a ^ !b ^ !ci)  v  (a ^ b ^ ci)  v  (!a ^ !b ^ ci) 
(defun pretty-display (expr)
  (mapcar 'display-with-spaces expr))

(defun display-with-spaces (expr)
  (progn (princ " ") (princ expr) (princ " ")))

;; (compact-display '(a ^ b ^ c)) -> a^!b^c
;; (compact-display '!a) -> !a
(defun compact-display (expr)
  (if (symbol? expr)
      (princ expr)
      (mapcar 'princ expr)))

(defun display-with-bracket (expr)
  (progn (princ "(")) (princ expr) (princ ")"))

;; this function start the display without bracket for the outside of complex expressions 
;; (compact-display-bracket '(a ^ !b ^ c)) -> a^!b^c
;; (compact-display-bracket '!a) -> !a
;;
;; ? (compact-display-bracket '((a ^ b ^ c) v (a ^ !c)))
;; (A^B^C)V(A^!C)
;; (")" V ")")
;;
;; (compact-display-bracket (dnf-infix-symb (symb-compute-sum 'Ci 'a 'b)))
;;    -> (!a^b^!ci)v(a^!b^!ci)v(a^b^ci)v(!a^!b^ci)

(defun compact-display-bracket (expr)
  (if (symbol? expr)
      (princ expr)
      (mapcar 'bracket-compact-display-bracket expr))) ;; display with bracket for sub-expressions
	

(defun bracket-compact-display-bracket (expr)
  (if (symbol? expr)
      (princ expr)
      (progn
	(princ "(")
	(mapcar 'compact-display-bracket expr) ;; no bracket for inner symbols
	(princ ")"))))


(defun pretty-display-condensed (expr)
  (if (or (symbol? expr) (symbol? (first expr)));; '!a, a, b, '(a ^ b ^ c), '(a ^ !b) ,...
      (compact-display expr)
      (mapcar 'compact-display-bracket expr))) ;; '((a ^ b ^ c) v (a ^ !b)) ,...
	  
;; just remove all the trash from displays....
;; (cleaner '(compact-display '(a ^ b ^ c))) 
;; A^B^C
;; and nothing else.... or almost (in Lisp :-( )
(defun cleaner (task)
  (progn
    (eval task)
    (princ "")))

;; another definition that use a macro
;; note that there is no more need to quote the argument when using a macro 
;;
;;  (mac-cleaner (compact-display '(a ^ b ^ c))) -> a^b^c
;;  (mac-cleaner (enlight-dnf (symb-compute-sum 'Ci 'a 'b))) -> (!a^!b^Ci)v(a^b^Ci)v(a^!b^!Ci)v(!a^b^!Ci)
(defmacro mac-cleaner (task) 
  `(progn
     ,task
     (princ "")))

;; put an expression in DNF in infix with symbols and all the simplifications
;;
;; with DrRacket:
;;  (dnf-infix-symb (symb-compute-sum 'Ci 'a 'b)) -> '((!a ^ !b ^ Ci) v (a ^ b ^ Ci) v (a ^ !b ^ !Ci) v (!a ^ b ^ !Ci))
;;
;; with MIT Scheme:
;; (dnf-infix-symb (symb-compute-sum 'Ci 'a 'b)) -> ((!a ^ b ^ !ci) v (a ^ !b ^ !ci) v (a ^ b ^ ci) v (!a ^ !b ^ ci))
(defun dnf-infix-symb (expr)
  (prefix->infix-symb (simplify-DNF-by-unitary-reduction (simplify (n-arity (simplify-OR (simplify-AND (dnf expr))))))))

;; put an expression in CNF in infix with symbols and all the simplifications
;;  (cnf-infix-symb (symb-compute-sum 'Ci 'a 'b)) -> '((a v b v Ci) ^ (!a v !b v Ci) ^ (!a v b v !Ci) ^ (a v !b v !Ci))
(defun cnf-infix-symb (expr)
  (prefix->infix-symb (simplify (n-arity (simplify-AND (simplify-OR (cnf expr)))))))

;; n-arity function, this version will not show AND & OR case but collect them in one single line code
;; n-arity single function replacing n-arity-or and n-arity-and and that use the collect-leaves function 
;; with no match special form inside them and no operator show
(defun n-arity (expr)
  
;;  > (n-arity (dnf (symb-compute-sum 'Ci 'a 'b)))
;;  '(or (and Ci (not a) a)
;;       (and Ci (not a) (not b))
;;       (and Ci b a)
;;       (and Ci b (not b))
;;       (and (not Ci) a (not b))
;;       (and (not Ci) (not a) b))

;;  > (n-arity '(or a (not b) (or (or (and c (and c2 c3)) d) e) (and (and (not f) g) h) (or i (and (not j) (and k (or l (or m (not n))))))) )
;;   (OR A (NOT B) (AND C C2 C3) D E (AND (NOT F) G H) I (AND (NOT J) K (OR L M (NOT N))))

  
;;  > (n-arity (cnf (symb-compute-sum 'Ci 'a 'b)))
;;  '(and (or Ci (not Ci))
;;        (or Ci a (not a))
;;        (or Ci a b)
;;        (or Ci (not b) (not a))
;;        (or Ci (not b) b)
;;        (or (not a) b (not Ci))
;;        (or (not a) b a (not a))
;;        (or (not a) b a b)
;;        (or (not a) b (not b) (not a))
;;        (or (not a) b (not b) b)
;;        (or a (not b) (not Ci))
;;        (or a (not b) a (not a))
;;        (or a (not b) a b)
;;        (or a (not b) (not b) (not a))
;;        (or a (not b) (not b) b))
;;  >   

 
(cond
 ((isOR? expr) (cons 'or (apply 'append (mapcar 'collect-leaves-OR (args expr)))))
 ((isAND? expr) (cons 'and (apply 'append (mapcar 'collect-leaves-AND (args expr)))))
 (T expr)))

      
; this is a version of collect-leaves-or that do not use the match special form
(defun collect-leaves-OR (expr)
  (cond
   ((isOR? expr) (apply 'append (mapcar 'collect-leaves-OR (args expr))))
   ((isAND? expr) (list (n-arity expr)))
   (T (list expr))))

(defun collect-leaves-AND (expr)
  (cond
   ((isAND? expr) (apply 'append (mapcar 'collect-leaves-AND (args expr))))
   ((isOR? expr) (list (n-arity expr)))
   (T (list expr))))


;; test if an operator is AND
(defun AND-op? (oper)
  (or (equal oper 'and) (equal oper 'AND)))

;; test if an operator is OR
(defun OR-op? (oper)
  (or (equal oper 'or) (equal oper 'OR)))


;; return the litteral of expression of type (not 'a) , 'a
;; in case of boolean return : NIL -> 'F , T -> 'T
(defun get-litteral (expr)
  (if (isNOT? expr)
      (first (rest expr))
      (if (boolean? expr)
	  (if expr 'T 'F)
	  expr))) 

;; return the litteral of expression of type (not 'a) , 'a
;; or return the first litteral of a binary expression (OR / AND) 
;; (get-first-litteral '(or a b)) -> 'a
;; (get-first-litteral '(or (not a) b)) -> 'a
(defun get-first-litteral (expr)
  (if (isOR-AND? expr)
      (get-litteral (first (rest expr)))
      (get-litteral expr))) 


;; search-not-lit
;; test if we have (not x) 
;; lit : litteral example: 'x 'b
;; lep : list of expressions ,example : '(a b (not x) c x (not a))
;;
;; (search-not-lit? 'c '(a b (not x) c x (not a))) -> NIL
;;
;; (search-not-lit? 'x '(a b (not x) c x (not a))) -> ((NOT X) C X (NOT A))
;;
(defun search-not-lit? (lit lep) ;; inputs are a litteral and a list of expressions
  (member1 (list 'not lit) lep))

;; la recherche de l'element a un niveau arbitraire
(defun member1 (ele liste)
  (cond
   ((atom liste) NIL)
   ((equal (car liste) ele) liste)
   (T (memb1 ele (member1 ele (car liste)) (cdr liste)))))

(defun memb1 (ele aux liste)
  (if aux aux (member1 ele liste)))

;; this is a function that behaves like the Scheme one
;;? (member2 'x '((not a) (or (not x) b) c))
;;NIL
;;? (member2 '(not x) '((not a) (or (not x) b) c))
;;NIL
;;? (member2 '(not a) '((not a) (or (not x) b) c))
;;T

(defun member2 (x L)
  (cond
   ((null L) NIL)
   ((equal (first L) x) T)
   (T (member2 x (rest L)))))

;; input : get an AND example: (AND x (not x) y z)
;; will check all operands of AND to see if there is an antilogy in it 
;;
;; > (is-AND-antilogy? '(and Ci (not a) a)) -> T
;; > (is-AND-antilogy? '(and (not Ci) a (not b))) -> NIL
(defun is-AND-antilogy? (expr)
  (let
      ((lep (args expr))) ;; list of expressions which could be litterals (ex 'b , 'x ) or negations (not (b))
					;
    (labels 
     ((detect-antilogy (listExpr)
		       (if (null listExpr) 
			   NIL
			 (if (symbol? (first listExpr)) ;; we search for a litteral ex: 'x    
			     (if (search-not-lit? (first listExpr) lep) ;; search antilogy with litteral and the whole operands of AND
				 T
			       (detect-antilogy (rest listExpr))) ;; check the rest of the list with another litteral
			   (detect-antilogy (rest listExpr)))))) ;; check the rest of the list to find a litteral                              
     (detect-antilogy lep))))

;; remove the antilogies out of a list of ANDed expressions... whaooo j'aime cette phrase...
;; (remove-antilogies '((and Ci (not a) a) (and Ci (not a) (not b)))) -> ((AND CI (NOT A) (NOT B)))
;;  (remove-antilogies '()) -> '()
;; (remove-antilogies '(Ci (and a b (not b)))) -> '(Ci)
(defun remove-antilogies (andList) ;; argument is a list of ANDed expressions
  (cond
   ((null andList) '())
   ((and (isAND? (first andList)) (is-AND-antilogy? (first andList))) (remove-antilogies (rest andList)))
   (T (cons (first andList) (remove-antilogies (rest andList))))))


;; input : get an OR example: (OR x (not x) y z)
;; will check all operands of OR to see if there is a tautology in it 
;;
;; >  (is-OR-tautology? '(or a (not b) (not b) (not a))) -> T
;; >  (is-OR-tautology? '(or a (not b) (not Ci))) -> NIL
(defun is-OR-tautology? (expr)
  (let
      ((lep (args expr))) ;; list of expressions which could be litterals (ex 'b , 'x ) or negations (not (b))
					; 
    (labels
     ((detect-tautology (listExpr)
			(if (null listExpr) 
			    NIL
			  (if (symbol? (first listExpr)) ;; we search for a litteral ex: 'x    
			      (if (search-not-lit? (first listExpr) lep) ;; search tautology with litteral and the whole operands of OR
				  T
				(detect-tautology (rest listExpr))) ;; check the rest of the list with another litteral
			    (detect-tautology (rest listExpr)))))) ;; check the rest of the list to find a litteral   
     (detect-tautology lep))))


;; remove the tautologies out of a list of ORed expressions...
;; (remove-tautologies  
;;   '((or Ci (not Ci))
;;     (or Ci a (not a))
;;     (or Ci a b)
;;     (or Ci (not b) (not a))
;;     (or Ci (not b) b)
;;     (or (not a) b (not Ci))
;;     (or (not a) b a (not a))
;;     (or (not a) b a b)
;;     (or (not a) b (not b) (not a))
;;     (or (not a) b (not b) b)
;;     (or a (not b) (not Ci))
;;     (or a (not b) a (not a))
;;     (or a (not b) a b)
;;     (or a (not b) (not b) (not a))
;;     (or a (not b) (not b) b)))
;; ->  '((or Ci a b) (or Ci (not b) (not a)) (or (not a) b (not Ci)) (or a (not b) (not Ci)))
;;
;;  (remove-tautologies '()) -> '()
(defun remove-tautologies (orList) ;; argument is a list of ORed expressions
  (cond
   ((null orList) '())
   ((and (isOR? (first orList)) (is-OR-tautology? (first orList))) (remove-tautologies (rest orList)))
   (T (cons (first orList) (remove-tautologies (rest orList))))))

;; simplify the expressions
;; (or e1 e2 .... eN)
;; if eI is an antilogy then remove it 
;;
;; (simplify-DNF (n-arity (dnf (symb-compute-sum 'Ci 'a 'b))))
;; -> '(or 
;;         (and Ci (not a) (not b)) 
;;         (and Ci b a)
;;         (and (not Ci) a (not b))
;;         (and (not Ci) (not a) b))
;;
;; (simplify-DNF '(or (and Ci b)  (and a b (not b)))) -> (AND CI B)
;;
;;;;  (simplify-DNF '(or Ci (and a b (not b)))) -> CI
;;
(defun simplify-DNF (dnfExpr)
  (if (is-OR-tautology? dnfExpr)
      T
    (let ((operandList (remove-antilogies (rest dnfExpr)))) ;; first we remove antilogies in the operands
      (if (null (rest operandList)) ;; if we have only one element in the result list
	  (first operandList) ;; we can forget the or operator
	(cons 'or operandList)))))

 
;; simplify the expressions
;; (and e1 e2 .... eN)
;; if eI is a tautology then remove it 
;;
;; (simplify-CNF (n-arity (cnf (symb-compute-sum 'Ci 'a 'b))))
;; -> '(and (or Ci a b) (or Ci (not b) (not a)) (or (not a) b (not Ci)) (or a (not b) (not Ci)))
;;
(defun simplify-CNF (cnfExpr)
  (if (is-AND-antilogy? cnfExpr)
      NIL
    (let ((operandList (remove-tautologies (rest cnfExpr)))) ;; first we remove tautologies in the operands
      (if (null (rest operandList)) ;; if we have only one element in the result list
	  (first operandList) ;; we can forget the or operator
	(cons 'and operandList)))))


;; simplify the DNF or CNF expressions
;;
;; (simplify-*NF (n-arity (cnf (symb-compute-sum 'Ci 'a 'b))))
;;    -> '(and (or a b Ci) (or (not a) (not b) Ci) (or (not a) b (not Ci)) (or a (not b) (not Ci)))
;;
;; (simplify-*NF '(and (or a (not a) a) (or Ci b Ci))) -> '(or b Ci)
;;
;;;; (simplify-*NF '(or (and Ci Ci)  (and a b (not b)))) -> 'Ci
;;
(defun simplify-*NF (norm-form)
  ;; first we will remove duplicates and sort arguments
  (let* ((arg-lst (args norm-form)) ;; define arguments list
	 (oper (operator norm-form)) ;; define operator
	 (arg-list-no-dup (mapcar 'remove-duplicates-in-operation arg-lst)) ;; argument list without duplicate elements
	 (arg-list-no-dup-sorted (mapcar 'sort-arguments-in-operation arg-list-no-dup));; argument list sorted
	 ;;(expr-no-dup (cons oper arg-list-no-dup)) ;; reconstruct expression with removed duplicate in operands
	 (expr-no-dup-sorted (cons oper arg-list-no-dup-sorted)))
    (if (equal (first expr-no-dup-sorted) 'and)
	(simplify-CNF expr-no-dup-sorted)
	(simplify-DNF expr-no-dup-sorted))))


;; simplify logical expressions by searching antilogies and tautologies in sub-expressions 
;; parameter : a normal form expression
;;
;; (simplify (n-arity (cnf (symb-compute-sum 'Ci 'a 'b))))
;;    -> '(and (or a b Ci) (or (not a) (not b) Ci) (or (not a) b (not Ci)) (or a (not b) (not Ci)))
;;
;; (simplify '(and b a b (not b))) -> #f
;;
;; (simplify '(and (or ci b) a (or a a))) -> '(and a (or b ci)) 
;; 
;;  (simplify '(and (or (not ci) b) d (not d) (or a a))) -> #f
;;
;; (simplify '(and (or (not ci) b) (or d  d)  d (or (not d) (not d)) (or a a))) -> #f
(defun simplify (expr)
  (cond 
   ((null expr) expr)
   ((symbol? expr) expr) 
   ((is-single-form? expr) (simplify-SF expr)) 
   (T (sort-arguments-in-operation (remove-duplicates-in-operation (simplify-*NF expr))))))

;; simplify Single Form
;; (simplify-SF  '(and b a b (not b))) -> NIL
(defun simplify-SF (expr)
  (let* ((oper (operator expr)) ;; define operator
	 (expr-no-dup (remove-duplicates-in-operation expr)) ;; remove duplicate symbols
	 (expr-no-dup-sorted (sort-arguments-in-operation expr-no-dup))) ;; sort variables
    (if (equal oper 'and) ;; AND => search for antilogies
	(if (is-AND-antilogy? expr-no-dup-sorted) NIL expr-no-dup-sorted)
	(if (is-OR-tautology? expr-no-dup-sorted) T expr-no-dup-sorted)))) ;;  OR => search for tautologies



;; sort operands in a logic expression
;; (sort-arguments-in-operation '(or Ci a b)) -> (OR A B CI)
;; (sort-arguments-in-operation '(or Ci (not a) b)) -> '(or (not a) b Ci)
;; (sort-arguments-in-operation '(or Ci (not a) b (or c d))) -> (OR (NOT A) B (OR C D) CI)
(defun sort-arguments-in-operation (expr)
  (if (isOR-AND? expr)
      (labels
       ((expression->string (expr2) (cond ((symbol? expr2) (symbol-name expr2)) ;; #t -> "T", #f -> "F"
					  ((boolean? expr2) (if expr2 "T" "F"))
					  (else (error "sort-arguments-in-operation: do not know how to handle an expression"))))
	(lower-litteral-symbol (s) (string-downcase (expression->string (get-first-litteral s)))) ;; 'Ci -> "ci", '(not A) -> "a"
	(expression<? (x y) (string< (lower-litteral-symbol x) (lower-litteral-symbol y))))
	(let* ((args-list (args expr)) ;;'(or Ci a b) -> '(Ci a b) 
	       ;;(sorted-args (sort args-list #:key lower-litteral-symbol string<?)) ;; symbol<?)) ;; '(Ci a b) -> '(a b Ci)
	       (sorted-args (sort args-list #'expression<?))
	       (oper (operator expr))) ;; define operator : (or Ci a b) -> or
	  (cons oper sorted-args))) ;; fin labels
    expr)) ;; we have not a binary operator but a litteral or negation of litteral


(defun empty? (lst)
  (null lst))

(defvar empty '())

;; insert an element in a list (at the end) if the element is not already included in the list
(defun insertNoDups (element lst)
  (cond
    ((empty? lst) (cons element lst))
    ((equal element (first lst)) lst)
    (T (cons (first lst) (insertNoDups element (rest lst))))))

(defvar else T) ;; histoire de rire...

;; commented for  Clozure CL because "The function REMOVE-DUPLICATES is predefined in Clozure CL".
;; remove-duplicates dans Clozure et GNU Common Lisp ne supprime pas les sous listes identiques
;; (remove-duplicates '((not a) a (not a))) ->  ((NOT A) A (NOT A))
;;
;;(defun remove-duplicates (lst)
;;  (cond
;;    ((empty? lst) empty)
;;    (else (insertNoDups (first lst) (remove-duplicates (rest lst))))))

(defun remove-duplicates-lisp (lst)
  (cond
    ((empty? lst) empty)
    (else (insertNoDups (first lst) (remove-duplicates-lisp (rest lst))))))

;; remove duplicates operands in a logic expression
;; (remove-duplicates-in-operation '(or a (not a) a)) -> (OR (NOT A) A)
;; (remove-duplicates-in-operation '(or a a)) -> A
(defun remove-duplicates-in-operation (expr)
  (if (isOR-AND? expr)
      (let ((expr-unik (remove-duplicates-lisp (rest expr)))) ;; remove duplicates from operands '(or a b a) -> '(a b)
	(if (null (rest expr-unik)) ;; test if we have only one element, example : '(a)
	    (first expr-unik) ;; return the single resting litteral '(a) -> a
	    (cons (first expr) expr-unik))) ;; construct a list with operator and uniques operands, example '(a b) -> '(or a b)
      expr)) ;; we have not a binary operator but a litteral or negation of litteral

;; test for a monomial negation
;; (is-monomial-NOT? '(not x)) -> T
;; (is-monomial-NOT? '(not (not x))) -> NIL
(defun is-monomial-NOT? (expr)
  (and (isNOT? expr) (symbol? (car (cdr expr)))))


;; predicate to know if an expression is a single form 
;;
;; examples of single forms: (not x) , (or x y z) , x
;; counter examples: (and (or x y))
;;
;; (is-single-form? 'x) -> T
;; (is-single-form? '(not x)) -> T
;; (is-single-form? '(not (not x))) -> NIL
;; (is-single-form? '(and (or x y))) -> NIL
;; (is-single-form? '(or x y z)) -> T
;; (is-single-form?  '(and a b (not b))) -> T
;;
(defun is-single-form? (expr)
  (cond
   ((symbol? expr) T) ;; test for a single litteral
   ((is-monomial-NOT? expr) T) ;; test for a monomial negation
   ((isNOT? expr) NIL)
   (else ;; we have a OR or AND
    ;; we check that all the arguments are litterals or single negations
    (flet ((litteral-or-single-negation? (q) (or (symbol? q) (is-monomial-NOT? q))))
      (andmap
       #'litteral-or-single-negation? ;; The hashquote is shorthand for (FUNCTION litteral-or-single-negation?).
       (args expr))))))


(defun andmap (f l)
  (if (null l)
      T
    (and (funcall f (car l))
	 (andmap f (cdr l)))))

;; convert a prefix negation to a symbolic infix form
;; (prefix-NOT->infix-symbolic-form '(not a))
;; !A
;; NIL
;;
;; (prefix-NOT->infix-symbolic-form '(not (and a b))) -> '|!(a and b)|
(defun prefix-NOT->infix-symbolic-form (expr)
  (let ((expr-arg (prefix->infix (first (rest expr))))) ;; get the litteral symbol
    (intern (concatenate 'string  "!" (symbol-name expr-arg))))) ;; Warning : this version can not handle expressions (but only symbols)
    ;;(string->symbol (string-append "!" (format "~s" expr-arg))))) ;; construct '!expr-arg

;; prefix->infix
;; a self explanatory name
;; works only for now with DNF and CNF
;;
;; (prefix->infix '(and a b)) -> (A AND B)
;; (prefix->infix '(and a b c d e)) -> '(a and b and c and d and e)
;; (prefix->infix '(and a (not b) c d e)) -> (A AND !B AND C AND D AND E)
;; (prefix->infix '(not (and a b)))  -> '|!(a and b)|    marche pas !!!
;; > (prefix->infix '(and a (not b) (not (or c d)) e))  -> '(a and !b and |!(c or d)| and e)
;; (prefix->infix (simplify-CNF (n-arity (cnf (symb-compute-sum 'Ci 'a 'b)))))
;; -> '((Ci or a or b) and (Ci or !b or !a) and (!a or b or !Ci) and (a or !b or !Ci))

(defun prefix->infix (expr)
  (cond
   ((null expr) expr)
   ((symbol? expr) expr)
   ((isNOT? expr) (prefix-NOT->infix-symbolic-form expr)) ;; (prefix->infix '(not a )) -> '!a
   (else (insert-op (first expr) (rest (mapcar 'prefix->infix expr))))))

;; prefix to infix notation with symbolic operators (v  ^)
;; prefix vers infix  avec des expressions en forme symbolique (v ^)
;; (prefix->infix-symb (simplify-CNF (n-arity (cnf (symb-compute-sum 'Ci 'a 'b)))))
;; -> '((Ci v a v b) ^ (Ci v !b v !a) ^ (!a v b v !Ci) ^ (a v !b v !Ci))
;; (prefix->infix-symb (simplify-*NF (n-arity (dnf (symb-compute-sum 'Ci 'a 'b)))))
;; -> '((!a ^ !b ^ Ci) v (a ^ b ^ Ci) v (a ^ !b ^ !Ci) v (!a ^ b ^ !Ci))
;; (prefix->infix-symb (simplify (n-arity (cnf (symb-compute-sum 'Ci 'a 'b)))))
;; -> '((a v b v Ci) ^ (!a v !b v Ci) ^ (!a v b v !Ci) ^ (a v !b v !Ci))
;; 
;; (prefix->infix-symb (simplify (n-arity (phase3 (simplify-negation (move-in-negations (elim-implications  (symb-compute-sum  'Cin 'A #t)))))))) -> '((!A ^ Cin ^ F) v (A ^ Cin ^ T) v (A ^ !Cin ^ F) v (!A ^ !Cin ^ T) v (Cin ^ F ^ T))
(defun prefix->infix-symb (expr)
  (cond
   ((null expr) expr)
   ((symbol? expr) expr)
   ((boolean? expr) (if expr 'T 'F)) ;; True and False
   ((isNOT? expr) (prefix-NOT->infix-symbolic-form expr)) ;; (prefix->infix-symb '(not a )) -> '!a
   (else (insert-op (alpha-op->symb-op (first expr)) (rest (mapcar 'prefix->infix-symb expr))))))

;; insert operator between variables where it should be to make an infix expression
(defun insert-op (op lst)
  ;; (insert-op 'and '(a b)) -> '(a and b)
  ;; (insert-op 'and '(a b c d)) -> '(a and b and c and d)
  (if (null (rest (rest lst)))
      (list (first lst) op (first (rest lst)))
    (cons (first lst) (cons op (insert-op op (rest lst)))))) ;; (insert-op 'and '(a b c)) -> '(a and b and c)


;; convert from alphabetic operators to symbolic operators
(defun alpha-op->symb-op (op)
  (cond
   ((equal op 'and) '^)
   ((equal op 'or) 'v)
   (else '?)))

(defun distribute-or-over-and  (expr1 expr2)  ;; expr1 et expr2 sont les arguments d'un 'or : ('or expr1 expr2)  
  ;; remember we have (expr1 or expr2) to distribute over the "and"
  (cond
   ((isAND? expr1)            ;; (expr1 expr2) <--> ( ('and p q) r )
    (let ((p (arg1 expr1))
	  (q (arg2 expr1))
	  (r expr2))
      `(and ,(distribute-or-over-and p r) ,(distribute-or-over-and q r)))) ;; (p and q) or r = (p or r) and (q or r)
   ((isAND? expr2)            ;; (expr1 expr2) <--> ( p ('and q r) )
    (let ((p expr1)
	  (q (arg1 expr2))
	  (r (arg2 expr2)))
      `(and ,(distribute-or-over-and p q) ,(distribute-or-over-and p r)))) ;; p or (q and r) = (p or q) and (p or r)
   (else `(or ,expr1 ,expr2)))) ;; else we create the expression ('or expr1 expr2) 


;; Conjunctive Normal Form
;; we make the 'and going out by distributing them over the 'or
;; PHASE 3 CNF: on fait au contraire sortir les 'and en distribuant les 'or
;; on ne s'occupe plus des négations !
(defun phase3-cnf (expr)
  (cond
   ((isAND? expr)
    (let ((p (arg1 expr))
	  (q (arg2 expr)))
      `(and ,(phase3-cnf p) ,(phase3-cnf q)))) ;; we do not distribute the 'and but apply phase3-cnf to arguments
   ((isOR? expr)
    (let ((p (arg1 expr))
	  (q (arg2 expr)))
      (distribute-or-over-and (phase3-cnf p) (phase3-cnf q)))) ;; apply distributivity to 'or
   (else expr))) ;; else we leave it unchanged (could be atom, not(x),... )



;; (cnf '(and (and a b) c)) -> '(and (and a b) c)
;; (cnf '(or (and a b) (and c d))) -> '(and (and (or a c) (or a d)) (and (or b c) (or b d)))
(defun cnf (expr)    ;; conjunctive normal form
  (phase3-cnf (move-in-negations (elim-implications expr))))

;; macro to use Scheme definition style in Lisp !!!
;; WARNING : this macro seems to not always works...
;; commented time to test it on different systems
;;(defmacro define (name_param body)
;;  `(defun ,(car name_param) ,(cdr name_param) ,body))

;; a simplification package for DNF in n-arity form
;;
;; (prefix->infix (simplify-n-arity-dnf (symb-compute-carry 'C 'a 'b)))
;;  -> ((A AND B) OR (A AND B AND !C) OR (A AND !B AND C) OR (!A AND B AND C))
;;
;;(define (simplify-n-arity-dnf expr)
;;  (simplify (n-arity (simplify-OR (simplify-AND (simplify-DNF-by-unitary-reduction (dnf expr)))))))

(defun simplify-n-arity-dnf (expr)
  (simplify (n-arity (simplify-OR (simplify-AND (simplify-DNF-by-unitary-reduction (dnf expr)))))))

;; exclusive or
(defun xor (p q) 
  ;; (xor #f #f) -> #f
  ;; (xor #t #f) -> #t
  (or (and p (not q)) (and (not p) q)))
  ;; (xor 0 0) -> 0
  ;; (xor 1 0) -> 1
  ;; (xor 1 1) -> 0
  ;;(logxor p q))

;; symbolic exclusive or
(defun symb-xor (p q) 
  ;; (symb-xor 'p 'q) -> '(or (and p (not q)) (and (not p) q))
  `(or (and ,p (not ,q)) (and (not ,p) ,q)))



;; adder circuit functions

;; symbolic functions
;;

;; compute Sum symbolically
;; return result of Cin + A + B (Cin being 'carry in')
(defun symb-compute-sum  (Cin A B)
  ;; (symb-compute-sum 'Ci 'a 'b) -> '(or (and Ci (not (or (and a (not b)) (and (not a) b)))) (and (not Ci) (or (and a (not b)) (and (not a) b))))
  (symb-xor Cin (symb-xor A B)))

(defun symb-compute-carry (Cin A B)
  ;; (symb-compute-carry 'Ci 'a 'b)
  ;; -> '(or (and (and a b) (not (and Ci (or (and a (not b)) (and (not a) b)))))
  ;;   (and (not (and a b)) (and Ci (or (and a (not b)) (and (not a) b)))))
  ;;
  ;; (enlight-dnf (symb-compute-carry 'Ci 'a 'b)) -> (a^b)v(a^b^!Ci)v(a^!b^Ci)v(!a^b^Ci)
  ;; (prefix->infix (simplify (n-arity (simplify-OR (simplify-AND (dnf (symb-compute-carry 'C 'a 'b)))))))
  ;;  -> ((A AND !B AND C) OR (!A AND B AND C) OR (A AND B) OR (A AND B AND !C)) 
  ;; todo: mettre sous forme disjonctive minimale
  (symb-xor `(and ,A ,B) `(and ,Cin  ,(symb-xor A B))))


;; non symbolic functions
;;

;; compute Cout, the 'carry out' of the result of Cin + A + B
(defun compute-carry (Cin A B)
  ;; (compute-carry #t #f #t) -> #t
  (xor (and A B) (and Cin (xor A B))))

(defun compute-sum (Cin A B)
  ;; (compute-sum #f #t #t) -> #f
  ;; (compute-sum #t #t #t) -> #t
  (xor Cin (xor A B)))

