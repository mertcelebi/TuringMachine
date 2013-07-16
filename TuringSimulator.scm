; ****************************************************************
; CS 201a
; ****************************************************************
; Name: Feridun Mert Celebi
; Email address: feridun.celebi@yale.edu
; ****************************************************************

; The topics of this assignment are:
; a simulator for Turing machines and
; writing Turing machine programs.

; ****************************************************************
; ** problem 0 ** (1 easy point)
; Modify the following definition to reflect the number of
; hours you spent on this assignment.

(define hours 6)

; ****************************************************************
; Turing machines were described in the lectures;
; see also the lecture notes on the course web page.
; Here is a top-level procedure to simulate a Turing machine
; starting from a given configuration until either
; it halts or it has executed n steps.
; The procedure returns the list of the successive configurations,
; starting with the initial one.
; The length of the list of configurations is one more than 
; the number of steps taken by the machine.

(define simulate 
  (lambda (mach config n)
    (cond
      ((<= n 0) (list config))
      ((halted? mach config) (list config))
      (else
       (cons config
             (simulate 
              mach (next-config mach config) (- n 1)))))))

; mach is a representation of a Turing machine
; config is a representation of a configuration of the machine
; n is the maximum number of steps to simulate

; The procedures halted? and next-config will be
; developed in the problems below; you will then
; have a complete Turing machine simulator.

; ****************************************************************
; A Turing machine is represented as a list of instructions, 
; where each instruction is a 5-tuple, represented as a list: 

; current state, current symbol, new state, new symbol, and move direction

; The current state and new state are Scheme symbols,
; the current symbol and new symbol are symbols or numbers,
; and the move direction must be either the symbol l or the symbol r.
; (NB: L and l are the same symbols in R5RS, as are R and r.)

; Example: (q1 0 q3 1 l)
; is an instruction
; with current state q1, current symbol 0,
; new state q3, new symbol 1,
; and move direction l.

; Here are selectors for the parts of an instruction:
; Please use them in your code -- they will be a lot more
; mnemonic than the corresponding list-refs or caddrs

(define i-state (lambda (inst) (list-ref inst 0)))
(define i-symbol (lambda (inst) (list-ref inst 1)))
(define i-new-state (lambda (inst) (list-ref inst 2)))
(define i-new-symbol (lambda (inst) (list-ref inst 3)))
(define i-direction (lambda (inst) (list-ref inst 4)))

; A Turing machine is simply a list of instructions.

; Example: a Turing machine that when started in state q1
; on the leftmost of a string of 0's and 1's 
; changes all the 0's to 1's and ; all the 1's to 0's 
; and then returns the head to the leftmost symbol and halts.

(define tm1 (list
             '(q1 0 q1 1 r)
             '(q1 1 q1 0 r)
             '(q1 b q2 b l)
             '(q2 0 q2 0 l)
             '(q2 1 q2 1 l)
             '(q2 b q3 b r)))

; ****************************************************************
; ** problem 1 (15 points)
; Define (in the format just given)
; a Turing machine named

; tm-double

; that makes a copy of its input string
; with each symbol repeated twice.

; That is, when started in state q1
; with the head on the leftmost of a
; string of 0's and 1's, it halts
; with the head on the leftmost of a
; string of 0's and 1's, and the
; output string is obtained from
; the input string by repeating each of its
; symbols twice.

; Your machine *may* use additional tape symbols
; but the output should contain no
; symbols other than 0, 1 and blank.
; When the machine halts, symbols
; other than the output should be blank.

; For example, the behavior of
; the machine should be:
; input  =>  output
; 110    =>  111100
; 101011 =>  110011001111
; 1      =>  11
; 0001   =>  00000011
; empty string => empty string

; (It may help to review ideas from the
; machine to make a copy of its input,
; described in lectures and in the 
; online lecture notes.)

; The initial state of your machine should
; be q1 -- other states may be named with
; Scheme symbols of your choice.

; IMPORTANT: please include an overview
; description of how your Turing machine works.
; Note that you'll be able to run it once you get
; the procedures for the simulator working.

; ****************************************************************

; This procedure, at its core, utilizes a class example Turing Machine
; that made a copy of its input.
(define tm-double (list
                   '(q1 0 q1 0 r) ; q1 runs to the end of the input configuration
                   '(q1 1 q1 1 r)
                   '(q1 b q2 c l) ; and writes a c and moves left to q2.
                   
                   '(q2 0 q2 0 l) ; q2 moves to beginning of the input by passing over
                   '(q2 1 q2 1 l) ; 1s and 0s.
                   '(q2 b q3 b r) ; Then it moves right into q3. 
                   
                   '(q2 c q2 c l) ; q2 skips over c moving left
                   '(q2 x q3 1 r) ; q2 replaces x by 1 and moves right into q3
                   '(q2 y q3 0 r) ; q2 replaces y by 0 and moves right into q3
                   
                   '(q3 1 q4 x r) ; q3 replaces 1 by x and moves right into q4
                   '(q3 0 q5 y r) ; q3 replaces 0 by y and moves right into q5
                   '(q3 c q6 c l) ; when q3 reads c, the whole input has been copied
                   
                   '(q4 1 q4 1 r) ; q4 moves to the right over 0's, 1's and c's to a blank
                   '(q4 0 q4 0 r)
                   '(q4 c q4 c r)
                   '(q4 b q9 1 l) ; q4 replaces blank with 1 and turns left into q9.
                   '(q9 1 q9 1 l)
                   '(q9 0 q9 0 l) ; q9 goes until it sees c.
                   '(q9 c q10 c r) ; this part of the procedure is modified so it doubles the input.
                   '(q10 1 q10 1 r)
                   '(q10 0 q10 0 r)
                   '(q10 b q2 1 l) ; q10 replaces blank by 1 and moves left into q2
                   
                   '(q5 1 q5 1 r) ; q5 moves to the right over 0's, 1's and c's to a blank
                   '(q5 0 q5 0 r)
                   '(q5 c q5 c r)
                   '(q5 b q11 0 l) ; q5 replaces blank with 1 and turns left into q11.
                   '(q11 1 q11 1 l)
                   '(q11 0 q11 0 l) ; q11 goes until it sees c.
                   '(q11 c q12 c r) ; this part of the procedure is modified so it doubles the input.
                   '(q12 1 q12 1 r)
                   '(q12 0 q12 0 r)
                   '(q12 b q2 0 l) ; q12 replaces blank by 1 and moves left into q2
                   
                   '(q6 0 q6 0 l)  ; q6 moves left over 0 and 1 to a blank
                   '(q6 1 q6 1 l)
                   '(q6 b q7 b r) ; on a blank q6 moves right into q7
                   
                   '(q7 1 q7 b r) ; then q7 replaces every 1 and 0 with a blank. 
                   '(q7 0 q7 b r)
                   '(q7 c q8 b r))) ; finally q7 replaces the  c and moves right into q8, the halt state.

; ****************************************************************
; ** problem 2 (10 points) - Done
; Write the following two procedures.
; Please use the instruction selectors defined above:
; i-state, i-symbol, i-new-state, i-new-symbol, i-direction

; (i-match? state symbol inst)
; returns #t if state and symbol are equal to 
; the state and symbol of instruction inst
; otherwise returns #f

; (i-lookup state symbol mach)
; returns #f if no instruction of Turing machine mach 
; has state and symbol equal to state and symbol
; otherwise returns the instruction in mach that matches.
; You may assume that at most one instruction will match.

; Examples:
; (i-match? 'q1 'b '(q1 b q3 b l)) => #t
; (i-match? 'q1  0 '(q1 1 q4 1 l)) => #f
; (i-match? 'q2 1 '(q2 1 q2 1 l)) => #t
; (i-lookup 'q1 1 tm1) => (q1 1 q1 0 r)
; (i-lookup 'q2 'b tm1) => (q2 b q3 b r)
; (i-lookup 'q3 1 tm1) => #f

; ****************************************************************

(define i-match?
  (lambda (state symbol inst)
    (if (and (equal? state (i-state inst))
             (equal? symbol (i-symbol inst)))
        #t
        #f)))

(define i-lookup
  (lambda (state symbol mach)
    (cond
      ((null? mach) #f)
      ((and (equal? state (i-state (car mach)))
            (equal? symbol (i-symbol (car mach)))) (car mach))
      (else (i-lookup state symbol (cdr mach))))))

; ****************************************************************
; A Turing machine tape-head configuration is a list of 3 items:

; (1) the tape contents to the left of the head
; (2) the symbol scanned by the read/write head
; (3) the tape contents to the right of the head

; where
; (1) is a list of Scheme numbers or symbols
; (2) is a single Scheme number or symbol
; (3) is a list of Scheme numbers or symbols

; The symbol b represents a blank -- the symbols to the
; left of (1) and the right of (3) are assumed to be
; blanks.

; Examples: two tape-head configurations

(define th-config1 '((1 1) 0 (1 0)))
(define th-config2 '(() b (b 0 1 b 1 b)))

; In th-config1, the non-blank tape contents are 1, 1, 0, 1, 0,
; surrounded by blanks, and the head is on the first 0.
; In th-config2 the tape is blank to the left of the head, the
; head is on a blank, and the symbols to the right of the
; head are b, 0, 1, b, 1, b, followed by blanks.

; Here are selectors for a tape/head configuration.
; Please use them to access parts of a tape/head
; configuration instead of car, cdr, or list-ref.

(define th-left (lambda (th-config) (car th-config)))
(define th-symbol (lambda (th-config) (cadr th-config)))
(define th-right (lambda (th-config) (caddr th-config)))

; A tape/head configuration is *normalized* if the
; th-left part has no initial b symbols and the
; th-right part has no final b symbols.
; Thus, th-config1 is normalized, but th-config2 is not,
; because its th-right part ends with the symbol b.

; ****************************************************************
; ** problem 3 (10 points) - Done
; Write the following two procedures.
; Please use the selectors th-left, th-symbol, th-right
; to access parts of a tape/head configuration

; (th-normalize th-config)
; takes a tape-head configuration th-config and
; returns an equivalent *normalized* tape/head configuration.
; That is, all the initial b symbols of the th-left part
; are removed, and all the final b symbols of the th-right
; part are also removed.

; (write-symbol new-symbol th-config)
; takes a normalized tape/head configuration th-config and
; returns a normalized tape/head configuration
; in which the symbol scanned by the read/write head
; has been replaced by new-symbol.

; Examples:
; (th-normalize '((b 0) b (1 1 0 b b))) => ((0) b (1 1 0))
; (th-normalize '((b b) b (b b b))) => (() b ())
; (th-normalize '((b 0 b 0) 1 (0 b 0 b))) => ((0 b 0) 1 (0 b 0))
; (write-symbol 'x '((0) b (1 1 0))) => ((0) x (1 1 0))
; (write-symbol 'c '((0 0) 1 (1 1 1))) => ((0 0) c (1 1 1))
; (write-symbol 'b '(() b ())) => (() b ())
; ****************************************************************

; This remove procedure receives two arguments: one element and one list.
; This procedure scans the list and tries to find the element. If it can find
; the element it removes from the list.
(define remove
  (lambda (element lst)
    (cond
      ((equal? '() lst) '())
      ((equal? (car lst) element) (remove element (cdr lst)))
      (else (cons (car lst) (remove element (cdr lst)))))))

; This procedure receives a list and the length of the list.
; It basically removes the last element of the list by taking the
; car and cdr of the list several times.
(define remove-last
  (lambda (lst len)
    (cond
      ((or (equal? '() lst) (= len 1)) '())
      (else
       (cons (car lst) (remove-last (cdr lst) (- len 1)))))))

(define th-normalize
  (lambda (th-config)
    (let ((right (th-right th-config)) (left (th-left th-config)))
      (cond
        ((and (null? left )
              (null? right)) th-config)
        ((and (not (null? left)) (equal? 'b (car left))
              (th-normalize (cons (cdr left) (cdr th-config)))))
        ((and (not (null? right)) (equal? 'b (list-ref right (- (length right) 1)))
              (th-normalize (append (remove right th-config) (list (remove-last right (length right)))))))
        (else
         th-config)))))

(define write-symbol
  (lambda (new-symbol th-config)
    (let ((right (th-right th-config)) (left (th-left th-config)))
      (append (list left) (append (list new-symbol) (list right))))))

; ****************************************************************
; ** problem 4 ** (10 points) - Done
; Write two procedures

; (shift-head-left th-config)
; takes a normalized tape-head configuration th-config and
; returns a normalized tape-head configuration in which
; the position of the read/write head has been moved one
; tape square to the left.

; (shift-head-right th-config)
; takes a normalized tape-head configuration th-config and
; returns a normalized tape-head configuration in which
; the position of the read/write head has been moved one
; tape square to the right.

; Examples:
; (shift-head-left '(() b ())) => (() b ())
; (shift-head-left '((0 0) 1 (1 1))) => ((0) 0 (1 1 1))
; (shift-head-left '(() 0 (1 1 0))) => (() b (0 1 1 0))
; (shift-head-right '(() b ())) => (() b ())
; (shift-head-right '(() 0 (1 1 1))) => ((0) 1 (1 1))
; (shift-head-right '((1 0 1) 1 ())) => ((1 0 1 1) b ())
; ****************************************************************

(define shift-head-left
  (lambda (th-config)
    (let ((right (th-right th-config)) (left (th-left th-config)) (middle (th-symbol th-config)))
      (cond
        ((null? left) (th-normalize (write-symbol 'b (cons left (list middle (cons middle right))))))
        (else
         (th-normalize (write-symbol (list-ref left (- (length left) 1))
                                     (cons (remove-last left (length left)) (list middle (cons middle right))))))))))

(define shift-head-right
  (lambda (th-config)
    (let ((right (th-right th-config)) (left (th-left th-config)) (middle (th-symbol th-config)))
      (cond
        ((null? right) (th-normalize (write-symbol 'b (cons (append left (list middle)) (append (list middle '()))))))
        (else
         (th-normalize (write-symbol (car right) (cons (append left (list middle)) (append (list middle) (list (cdr right)))))))))))

; ****************************************************************
; A machine configuration is a list of two items:
; (1) the current state of the machine (a Scheme symbol)
; (2) a *normalized* tape-head configuration

; Example: a configuration with state q1, tape
; contents: blanks, 1, 1, 0, 1, 0, blanks, and
; the head on the leftmost non-blank square.

(define config1 '(q1 (() 1 (1 0 1 0))))

; Here are selectors for the parts of a machine configuration.
; Use them in your code rather than car, cdr, or list-ref.

(define c-state (lambda (config) (car config)))
(define c-th (lambda (config) (cadr config)))

; ****************************************************************
; ** problem 5 ** (10 points) - Done
; Write the following two procedures.

; (c-symbol config)
; given a machine configuration, returns
; the symbol currently scanned by the read/write head.

; (halted? mach config)
; that returns #t if the Turing machine mach is halted in 
; machined configuration config (ie, no instruction of the
; machine matches the current state and symbol in
; configuration) and #f otherwise.

; Examples:
; (c-symbol '(q6 ((0 0) 1 (1)))) => 1
; (c-symbol '(q4 (() b ()))) => b
; (c-symbol '(q17 ((1 1 1) 0 (b 0 0)))) => 0
; (halted? tm1 config1) => #f
; (halted? tm1 '(q3 (() b (0 0 1 0 1)))) => #t
; (halted? '((q1 b q1 b r)) '(q1 (() b ()))) => #f
; ****************************************************************

(define c-symbol
  (lambda (config)
    (th-symbol (c-th config))))

(define halted?
  (lambda (mach config)
    (cond
      ((null? mach) #t)
      ((list? (i-lookup (c-state config) (c-symbol config) mach)) #f)
      (else #t))))

; ****************************************************************
; ** problem 6 ** (20 points) - You are almost there
; Write a procedure (next-config mach config)
; that returns the next configuration for the
; Turing machine mach in the configuration config.
; If there is no applicable instruction, the configuration
; returned should be just the input configuration.

; Hint: get your procedures
; halted?, i-lookup, write-symbol, shift-head-left, shift-head-right
; and combine them appropriately.

; Examples:
; (next-config tm1 config1) => (q1 ((0) 1 (0 1 0)))
; (next-config tm1 '(q1 ((0) 1 (0 1 0)))) => (q1 ((0 0) 0 (1 0)))
; (next-config tm1 '(q1 ((0 0 1 0) 0 ()))) => (q1 ((0 0 1 0 1) b ()))
; (next-config tm1 '(q1 ((0 0 1 0 1) b ()))) => (q2 ((0 0 1 0) 1 ()))
; (next-config tm1 '(q3 (() 0 (0 1 0 1)))) => (q3 (() 0 (0 1 0 1)))
; ****************************************************************

(define next-config
  (lambda (mach config)
    (let ((result (i-lookup (c-state config) (c-symbol config) mach))) 
      (cond
        ((halted? mach config) config)
        ((equal? (i-direction result) 'r)
         (cons (i-new-state result) (list (shift-head-right (write-symbol (i-new-symbol result) (c-th config))))))
        (else
         (cons (i-new-state result) (list (shift-head-left (write-symbol (i-new-symbol result) (c-th config))))))))))

; ****************************************************************
; If your procedures are working, then you should
; be able to run the following example, which
; shows the successive normalized configurations 
; of Turing machine tm1 when run from configuration config1.

;; > (simulate tm1 config1 12)
;; ((q1 (() 1 (1 0 1 0)))
;;  (q1 ((0) 1 (0 1 0)))
;;  (q1 ((0 0) 0 (1 0)))
;;  (q1 ((0 0 1) 1 (0)))
;;  (q1 ((0 0 1 0) 0 ()))
;;  (q1 ((0 0 1 0 1) b ()))
;;  (q2 ((0 0 1 0) 1 ()))
;;  (q2 ((0 0 1) 0 (1)))
;;  (q2 ((0 0) 1 (0 1)))
;;  (q2 ((0) 0 (1 0 1)))
;;  (q2 (() 0 (0 1 0 1)))
;;  (q2 (() b (0 0 1 0 1)))
;;  (q3 (() 0 (0 1 0 1))))

; ****************************************************************
; ** problem 7 ** (15 points)
; Define (in the given Scheme representation)
; a Turing machine named

; tm-subtract

; that takes as input two non-negative integers m and n
; in unary (separated by the symbol c) and
; produces as output the integer max(m-n, 0)
; in unary.  That is, if m > n, the result
; is m-n in unary, otherwise the result is
; 0 in unary (that is, no 1's).

; A number n is represented in unary by n 1's.
; The output of the machine should be
; a string of zero or more 1's representing the
; desired results.
; The read/write head should be on the leftmost
; nonblank symbol of the output (if any),
; and all other squares should be blank.

; You *may* use additional tape symbols.

; IMPORTANT: Include a clear overview
; description of how your Turing machine works.
; Give and justify a good upper bound on the
; number of steps your machine will take on
; an input of length n, as a function of n.

; NOTE: you can still do this problem if your simulator
; is not working, assuming you understand Turing machines
; and the Scheme representation of them given above.

; Examples
; input          => output
; 111c1          => 11
; 1111c11        => 11
; 111111c11      => 1111
; 1111c111       => 1
; 11c111         => empty string

; Here are input configurations if
; you want to simulate your tm-subtract on
; these inputs.

(define c3minus1 '(q1 (() 1 (1 1 c 1))))
(define c4minus2 '(q1 (() 1 (1 1 1 c 1 1))))
(define c6minus2 '(q1 (() 1 (1 1 1 1 1 c 1 1))))
(define c4minus3 '(q1 (() 1 (1 1 1 c 1 1 1))))
(define c2minus3 '(q1 (() 1 (1 c 1 1 1))))

; ****************************************************************

(define tm-subtract (list
                     '(q1 1 q1 1 r) ; q1 runs down to the end of the input
                     '(q1 c q1 c r)
                     '(q1 b q2 b l) ; q1 reaches the end and turns left into q2
                     '(q1 x q2 b l) ; q1 replaces x by 1 and moves right into q2
                     
                     '(q2 1 q3 x l) ; q2 puts an x for every 1 and turns left into q3
                     '(q2 c q5 b l) ; when q2 reads c, the right part has been completely subtracted.
                     
                     '(q3 1 q3 1 l) ; q3 moves to the beginning of the list over 1s and c.
                     '(q3 c q3 c l)
                     '(q3 b q4 b r) ; q3 moves right into q4 after it reaches the beginning of the list.
                     
                     '(q4 1 q1 b r) ; q4 deletes one 1 and moves right into q1.
                     '(q4 b q6 b r) ; if q4 runs into b, it starts replacing every element until it reaches the first x
                     '(q4 c q8 b r)
                     
                     '(q5 1 q5 1 l) ; q5 moves the cursor to the appropriate point.
                     '(q5 b q7 b r)
                     '(q6 c q6 c r)
                     '(q8 x q9 b r) ; q8 removes x and replaces it with b, turning into q9.
                     '(q9 b q10 b l))) ; q9 sees a b and turns left into q10, the halting state.

; ****************************************************************
; ** problem 8 ** (9 points)
; Is there a machine with states: q1, q2, q3, q4, q5
; and tape alphabet symbols: blank, 0, 1 (no additional symbols)
; that 
; (1) uses only directions l and r,
; (2) has no instructions defined for q5, and
; (3) when started on a completely blank tape,
;     runs for *exactly* 44 steps and halts?

; When the machine halts, the tape may have any contents.
; Justify your answer and explain how you found it.
; Include relevant calculations or code.

; Hint: you may want to read about the "Busy Beaver" problem
; using online sources.

; ****************************************************************

; I tried to approach this problem from several perspectives. First of all, researching the busy beaver problem gave me the idea that creating a turing machine with abovementioned
; specifications is possible.

; My successfull approach was to analyze the turing machine examples on the internet. I tried to find 2 state, 3 symbol turing machines (they are the most prevalent ones) that had less than
; 44 steps to halt, so that I could modify it to get it to 44 steps. After a long search, I found a 2 state 3 symbol turing machine that halted at 38 steps.
; The source of the turing machine is: http://www.logique.jussieu.fr/~michel/ha.html#tm23. Then I modified this turing machine, by adding three more states and 6 more states.
; So, in the end, my turing machine (tm-question-8) returns 45 configurations, equaling 44 different states. 

; One of my other approaches was to come up with a new simulator who would test every single turing machine with 5 states and 3 symbols. If any of the final number of configurations 
; equaled 45, my tester procedure would return that Turing Machine. Nevertheless, because my procedure ran for an extremely long time (as expected), time restrictions
; did not allow my program to come up with a final answer.

; And my other approach was to build a turing machine from scratch. However, given the huge number of probable turing machines, I could not succeed in my endeavor.

(define tm-question-8 (list
                '(q1 b q2 1 r)
                '(q1 1 q2 0 l)
                '(q1 0 q3 1 r)
                
                '(q2 b q1 0 l)
                '(q2 1 q2 0 r)
                '(q2 0 q2 1 l)
                
                '(q3 0 q4 0 r)
                '(q3 b q4 b l)
                '(q4 b q3 1 r)
                
                '(q4 1 q3 0 l)
                '(q4 0 q5 1 r)))


; *************** end of hw3.scm *********************************

