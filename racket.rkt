#lang racket

(define (my-dict->list d)
  (sequence-fold (λ (ac a b) (cons `(,a ',b) ac)) '() (in-dict d)))

(define (make-hash2 ks vs)
  (foldl (λ (k v res) (hash-set res k v)) (hash) ks vs))
;========================
;==== FC interpretor ====
;========================

(define (int-assign-args names args)
  ;(map (λ (name arg) `[,name ',arg]) names args))
  (make-hash2 names args))

(define (int-find-block blocks label)
  (define found (findf (λ (block) (equal? label (car block))) blocks))
  (if found (cdr found) `(return ,`(have_no_block ,label))))


(define (int-run bs ctx stms)
  ;  (printf "<int-run>\n")
  ;  (printf "stms: ~a\n" stms)
  (define assignraw (if (> (length stms) 1) (drop-right stms 1) '()))
  (define assignments (map cdr assignraw))
  ;  (printf "assignments: ~a\n" assignments)
  (define context (foldl int-assign-nv ctx assignments))
  ;  (printf "context: ~a\n" context)
  (int-jump bs context (last stms))
  )

(define (int-assign-nv namevalue context)
  (int-assign (car namevalue) (cadr namevalue) context))

(define (int-assign name value context)
   ; (printf "<int-assign>\n")
   ; (printf "assign context: ~a\n" context)
   ; (printf "assign namevalue ~a\n" namevalue)
  (hash-set context name (int-eval context value)))


(define (int-run-block bs ctx blockname)
   ; (printf "<int-run-block>\n")
  ; (printf "\n === run block name: ~a\n" blockname)
  (int-run bs ctx (int-find-block bs blockname)))

(define (int-eval context expr)
  ;(printf "\n<int-eval>\n")
  (define ctx (my-dict->list context))
  ;(printf " == eval context: ~a\n" ctx)
  (printf " == eval expr: ~a\n\n" expr)
  (define ans (eval `(let ,(my-dict->list context) ,expr)))
  (if (equal? expr 'm0-blocks-in-pending)
      (printf "\n>>>>> m0-blockcopy = ~a in? ~a; ~a\n" (dict-ref context 'm0-pp (λ () (printf ""))) ans (current-seconds))
      (printf ""))
   ans)

(define (int-jump blocks ctx jumpblock)
  (match (car jumpblock)
    ['goto (int-run-block blocks ctx (cadr jumpblock))]
    ['if (int-run-block blocks ctx 
          (if (int-eval ctx (cadr jumpblock)) (caddr jumpblock) (cadddr jumpblock)))]
    ['return (int-eval ctx (cadr jumpblock))])
  )

(define (int program data)
  (define readblock (car program))
  (define blocks (cdr program))
  (define context (int-assign-args (cdr readblock) data))
  (int-run blocks context (cdar blocks))
  )

(define (extract-names expr) '())

; FC program

(define find_name
  '((read name namelist valuelist)
    (search (if (equal? name (car namelist)) found cont))
    (cont (:= valuelist (cdr valuelist))
          (:= namelist (cdr namelist))
          (goto search))
    (found (return (car valuelist)))
    ))

;========================
;==== TM interpretor ====
;========================

(define (tm-goto number program) (memf (λ (inst) (equal? (car inst) number)) program))

(define int-tm '(
  (read program Right)
  ("main" (:= Left '())
        (:= cur (car Right))
        (:= Right (cdr Right))
        (:= progtail program)
        (goto "next-instruction"))
  ("next-instruction" (if (empty? progtail) "complete" "next-instruction-ok"))
  ("next-instruction-ok"
        (:= inst (car progtail))
        (:= instname (cadr inst))
        (:= progtail (cdr progtail))
        (goto "check-left"))
  ("check-left" (if (equal? instname 'left) "found-left" "check-right"))
  ("check-right" (if (equal? instname 'right) "found-right" "check-write"))
  ("check-write" (if (equal? instname 'write) "found-write" "check-goto"))
  ("check-goto" (if (equal? instname 'goto) "found-goto" "check-if"))
  ("check-if" (if (equal? instname 'if) "found-if" "match-error"))
  ("match-error" (return (string-append "mismatch with " (~a instname))))
  ("found-left" (:= Right (cons cur Right))
              (:= cur (if (empty? Left) '() (car Left)))
              (:= Left (if (empty? Left) '() (cdr Left)))
              (goto "next-instruction"))
  ("found-right" (:= Left (cons cur Left))
               (:= cur (if (empty? Right) '() (car Right)))
               (:= Right (if (empty? Right) '() (cdr Right)))
               (goto "next-instruction"))
  ("found-write" (:= cur (caddr inst))
               (goto "next-instruction"))
  ("found-goto" (:= next (caddr inst))
              (goto "run-goto"))
  ("found-if" (:= next (last inst))
            (if (equal? (caddr inst) cur) "run-goto" "next-instruction"))
  ("run-goto" (:= progtail (tm-goto next program))
            (goto "next-instruction"))
  ("complete" (return (append `(,cur) Right)))
  ))

;==========================
;==== first task tests ====
;==========================

(define check `(int find_name '(y (x y z) (1 2 3))))
(define tm-example '((0 if 0 goto 3) (1 right) (2 goto 0) (3 write 1)))
(define check-tm '(int int-tm `(,tm-example (1 1 1 0 1 0 1))))
;(define check-st '(() ([x 3] [y 7])))



;=======================
;==== SPECIALIZATOR ====
;=======================



(define (is-static-exp exp div)
  ;(printf "ise ~a ~a\n" exp div)
  (if (list? exp) ; we can't use lambdas and lets in flow-chart code
      (andmap [λ (x) (is-static-exp x div)] exp)
      (not (member exp (cadr div)))
      ))

(define (mix-reduce exp vs)
  ;(printf "\nmix-reduce exp:[~a] vs:{~a}\n\n" exp vs)
  (with-handlers
      ([(λ (v) #t)
        (λ (err)
          ;[printf "error: [~a] eval with exp: ~a, list: ~a\n" err exp (list? exp)]
          [if (list? exp) `,(map (λ (x) (mix-reduce x vs)) exp) exp])
        ])
    (if (and [list? exp] [and [not (empty? exp)] [equal? 'quote (first exp)]]) exp (let ([result (int-eval vs exp)]) ;(printf "reduce-result:[~a]\n" result)
      (if (procedure? result) exp (if (list? result) `',result result))))
    ))

(define (mix-pending-upd p pp1 pp2 vs marked)
  (define pv1 `(,pp1 ,vs))
  (define pv2 `(,pp2 ,vs))
  (define p1 (if (set-member? pv1 marked) p (cons pv1 p)))
  (if (set-member? pv2 marked) p1 (cons pv2 p1))
  )

(define (run-mix0 prog div vs0) (change-labels (int mix0 `(,prog ,div ,vs0))))
(define (run-mix1 prog div vs1) (change-labels (int mix1 `(,prog ,div ,vs1))))

; division - list of statics and list of dynamics
(define mix0 '(
   (read m0-program m0-div m0-vs0)
   ("mix0-main" (:= m0-pp0 (caadr m0-program))
              (:= m0-pending (set [list m0-pp0 m0-vs0]))
              (:= m0-blocks-in-pending (list m0-pp0))
              (:= m0-marked (set))
              (:= m0-residual (list [car m0-program])) ; save read block
              (goto "mix0-while1"))
   ("mix0-while1" (if (set-empty? m0-pending) "mix0-end" "mix0-cont1"))
   ("mix0-cont1" (:= m0-ppvs (set-first m0-pending))
               (:= m0-pp (car m0-ppvs))
               (:= m0-vs (cadr m0-ppvs))          
               (:= m0-pending (set-rest m0-pending))
               (:= m0-marked (set-add m0-marked m0-ppvs))
               (:= m0-code (list m0-ppvs))
               (goto "mix0-lookup-init"))
   ("mix0-lookup-init"
    (:= m0-blockcopy m0-blocks-in-pending)
               (:= m0-pps (car m0-blockcopy))
               (goto "mix0-lookup"))
   ("mix0-lookup"  (if (equal? m0-pp m0-pps) "mix0-foundpp" "mix0-notfoundpp"))
   ("mix0-foundpp" (:= m0-bb (int-find-block m0-program m0-pps))
                   (goto "mix0-while2"))
   ("mix0-notfoundpp" (:= m0-blockcopy (cdr m0-blockcopy))
                      (if (empty? m0-blockcopy) "mix0-pperror" "mix0-looknext"))
   ("mix0-looknext"   (:= m0-pps (car m0-blockcopy))
                      (goto "mix0-lookup"))
   ("mix0-pperror" ;(:= m0-residual (cons (string-append "error: can't lookup for " (~a m0-pp)) m0-residual))
                   ;(return (reverse m0-residual)))
                   (return "lookup error"))
   
   ("mix0-while2" (if (empty? m0-bb) "mix0-while2-end" "mix0-cont2"))
   ("mix0-cont2" (:= m0-command (car m0-bb))
                 (:= m0-bb (cdr m0-bb))
                 (:= m0-case (car m0-command))
                 (goto "mix0-check-assign"))
   ("mix0-check-assign" (if (equal? m0-case ':=)     "mix0-found-assign" "mix0-check-goto"))
   ("mix0-check-goto"   (if (equal? m0-case 'goto)   "mix0-found-goto"   "mix0-check-if"))
   ("mix0-check-if"     (if (equal? m0-case 'if)     "mix0-found-if"     "mix0-check-return"))
   ("mix0-check-return" (if (equal? m0-case 'return) "mix0-found-return" "mix0-match-error"))

   ("mix0-match-error" (return (string-append "mismatch with " (~a m0-case))))

   ("mix0-found-assign" (if [is-static-exp (cadr m0-command) m0-div] "mix0-static-assign" "mix0-dynamic-assign"))
   ;("mix0-found-goto"   (:= m0-pp (cadr m0-command))
   ;                     (goto "mix0-lookup-init"))
   ("mix0-found-goto"   (:= m0-bb [int-find-block m0-program (cadr m0-command)])
                        (goto "mix0-while2"))
   ("mix0-found-if"     (:= m0-ifexp (cadr m0-command))
                      (:= m0-ifpp1 (caddr m0-command))
                      (:= m0-ifpp2 (cadddr m0-command))
                      (if [is-static-exp m0-ifexp m0-div] "mix0-static-cond" "mix0-dynamic-cond"))
   ("mix0-found-return" (:= m0-code [cons (list 'return (mix-reduce (cadr m0-command) m0-vs)) m0-code])
                      (goto "mix0-while2"))
   
   ("mix0-static-assign" (:= m0-vs (int-assign (cadr m0-command) (caddr m0-command) m0-vs))
                       (goto "mix0-while2"))
   ("mix0-dynamic-assign" (:= m0-code (cons (list ':= (cadr m0-command) (mix-reduce (caddr m0-command) m0-vs)) m0-code))
                        (goto "mix0-while2"))

   ("mix0-static-cond" (if (int-eval m0-vs m0-ifexp) "mix0-if-true" "mix0-if-false"))
   ;("mix0-if-true" (:= m0-pp m0-ifpp1)
   ;                (goto "mix0-lookup-init"))
   ("mix0-if-true" (:= m0-bb (int-find-block m0-program m0-ifpp1))
                   (goto "mix0-while2"))
   ;("mix0-if-false" (:= m0-pp m0-ifpp2)
   ;                 (goto "mix0-lookup-init"))
   ("mix0-if-false" (:= m0-bb (int-find-block m0-program m0-ifpp2))
                    (goto "mix0-while2"))
   ("mix0-dynamic-cond" (:= m0-pending (set-union m0-pending
                                                (set-subtract (set (list m0-ifpp1 m0-vs) (list m0-ifpp2 m0-vs))
                                                               m0-marked)))
                        (:= m0-blocks-in-pending (set-add (set-add m0-blocks-in-pending m0-ifpp1) m0-ifpp2))
                        (:= m0-code (cons
                                   (list 'if (mix-reduce m0-ifexp m0-vs) (list m0-ifpp1 m0-vs) (list m0-ifpp2 m0-vs))
                                   m0-code))
                        (goto "mix0-while2"))
   ("mix0-while2-end"   (:= m0-residual (cons (reverse m0-code) m0-residual))
                        (goto "mix0-while1"))
   ("mix0-end"          (return (reverse m0-residual)))
   )
  )

(define mix1 '( ; copy-paste
   (read m1-program m1-div m1-vs0)
   (mix1-main (:= m1-pending (set [list (caadr m1-program) m1-vs0]))
              (:= m1-marked (set))
              (:= m1-residual (list [car m1-program])) ; save read block
              (goto mix1-while1))
   (mix1-while1 (if (set-empty? m1-pending) mix1-end mix1-cont1))
   (mix1-cont1 (:= m1-ppvs (set-first m1-pending))
               (:= m1-pending (set-rest m1-pending))
               (:= m1-marked (set-add m1-marked m1-ppvs))
               (:= m1-bb (int-find-block m1-program (car m1-ppvs)))
               (:= m1-vs (cadr m1-ppvs))
               (:= m1-code (list m1-ppvs))
               (:= m1-debug (length (set->list m1-pending)))
               (goto mix1-while2))
   (mix1-while2 (if (empty? m1-bb) mix1-while2-end mix1-cont2))
   (mix1-cont2 (:= m1-command (car m1-bb))
               (:= m1-bb (cdr m1-bb))
               (:= m1-case (car m1-command))
               (goto mix1-check-assign))
   (mix1-check-assign (if (equal? m1-case ':=)     mix1-found-assign mix1-check-goto))
   (mix1-check-goto   (if (equal? m1-case 'goto)   mix1-found-goto   mix1-check-if))
   (mix1-check-if     (if (equal? m1-case 'if)     mix1-found-if     mix1-check-return))
   (mix1-check-return (if (equal? m1-case 'return) mix1-found-return mix1-match-error))

   (mix1-match-error (return (string-append "mismatch with " (~a m1-case))))

   (mix1-found-assign (if [is-static-exp (cadr m1-command) m1-div] mix1-static-assign mix1-dynamic-assign))
   (mix1-found-goto   (:= m1-bb [int-find-block m1-program (cadr m1-command)])
                      (goto mix1-while2))
   (mix1-found-if     (:= m1-ifexp (cadr m1-command))
                      (:= m1-ifpp1 (caddr m1-command))
                      (:= m1-ifpp2 (cadddr m1-command))
                      (if [is-static-exp m1-ifexp m1-div] mix1-static-cond mix1-dynamic-cond))
   (mix1-found-return (:= m1-code [cons (list 'return (mix-reduce (cadr m1-command) m1-vs)) m1-code])
                      (goto mix1-while2))
   
   (mix1-static-assign (:= m1-vs (int-assign (cadr m1-command) (caddr m1-command) m1-vs))
                       (goto mix1-while2))
   (mix1-dynamic-assign (:= m1-code (cons (list ':= (cadr m1-command) (mix-reduce (caddr m1-command) m1-vs)) m1-code))
                        (goto mix1-while2))

   (mix1-static-cond (if (int-eval m1-vs m1-ifexp) mix1-if-true mix1-if-false))
   (mix1-if-true (:= m1-bb (int-find-block m1-program m1-ifpp1))
                 (goto mix1-while2))
   (mix1-if-false (:= m1-bb (int-find-block m1-program m1-ifpp2))
                  (goto mix1-while2))
   (mix1-dynamic-cond (:= m1-pending (set-union m1-pending
                                                (set-subtract (set (list m1-ifpp1 m1-vs) (list m1-ifpp2 m1-vs))
                                                               m1-marked)))
                      (:= m1-code (cons
                                   (list 'if (mix-reduce m1-ifexp m1-vs) (list m1-ifpp1 m1-vs) (list m1-ifpp2 m1-vs))
                                   m1-code))
                      (goto mix1-while2))
   (mix1-while2-end (:= m1-residual (cons (reverse m1-code) m1-residual))
                    (goto mix1-while1))
   (mix1-end (return (reverse m1-residual)))
   )
  )

(define mix-d '( ; danya
   (read program_1 divivision_1 vs0_1)
   (main (:= dynamic-args_1 (remove* division_1 (program-args program_1)))
         (:= init-pp_1 (init-point program_1))
         (:= pending_1 (list (cons init-pp_1 vs0_1)))
         (:= marked_1 pending_1)
         (:= residual_1 (list (cons 'read dynamic-args_1)))
         (goto pending-loop))
   (pending-loop (if (equal? pending_1 '()) pending-loop-end pending-loop-body))
   (pending-loop-end (return residual_1))
   (prending-loop-body (:= pp_1 (caar pending_1))
                       (:= vs_1 (cdar pending_1))
                       (:= pending_1 (cdr pending_1))
                       (:= code_1 (initial-block-code pp_1 vs_1))
                       (:= blocks-list_1 (cdr program_1))
                       (goto block-search))
   (block-search (if (equal? bock-list_1 '()) block-search-error block-search-ok))
   (block-search-error (return (list 'error: 'unknown 'label pp_1)))
   (block-search-ok (if (equal? pp_1 (caar blocks-list_1)) block-search-found block-search-next))
   (block-search-next (:= blocks-list_1 (cdr blocks-list_1))
                      (goto block-search))
   (block-search-found (:= bb_1 (cdar blocks-list_1))
                       (:= blocks-list_1 '())
                       (goto block-loop))
   (block-loop (if (equal? bb_2 '()) block-loop-end block-loop-body))
   (block-loop-end (:= residual_1 (add-block code_1 residual_1))
                   (:= command_1 '())
                   (goto pending-loop))
   (block-loop-body (:= command_1 (car bb_1))
                    (:= bb_1 (cdr bb_1))
                    (goto switch))
   (switch (if (equal? (car command_1) ':=) do-assn case1))
   (case1 (if (equal? (car command_1) 'goto) do-goto case2))
   (case2 (if (equal? (car command_1) 'if) do-if case3))
   (case3 (if (equal? (car command_1) 'return) do-return error))
   (error (return (list 'error: 'unknown 'command (car command_1))))
   (do-assn (:= X_1 (cadr command_1))
            (:= exp_1 (caddr command_1))
            (if (member X_1 division_1) static-assn dynamic-assn))
   (static-assn (:= vs_1 (list-set-v (index-of division_1 X_1) (...)))
                (:= X_1 '())
                (:= exp_1 '())
                (goto block-loop))
   (dynamic-assn (:= code_1 (add-instr (list ':= X_1 (reduce exp_1))))
                 (:= X_1 '())
                 (:= exp_1 '())
                 (goto block-loop))
   (do-goto (:= bb_1 (lookup (cadr command_1) (cdr program_1)))
            (goto block-loop))
   (do-if (:= reduce-res_1 (check-reduce (cadr command_1)) dynamic-args_1)
          (:= cond-res_1 (cdr (reduce-res_1)))
          (:= ppt_1 (caddr command_1))
          (:= ppf_1 (cadddr command_1))
          (if (check-condition (cadr command_1) dynamic-vars_1) static-if dynamic-if))
   (static-if (if (my-eval cond-res_1) static-ift static-iff))
   (static-ift (:= bb_1 (lookup ppt_1 (cdr program_1)))
               (:= ppt_1 '())
               (:= ppf_1 '())
               (goto block-loop))
   (static-iff (:= bb_1 (lookup ppf_1 (cdr program_1)))
               )
         
         ))

;=============================
;==== Specializator tests ====
;=============================

(define test_static1 '(is-static-exp '(+ 1 (* x 4)) '((x) ()))) ;#t
(define test_static2 '(is-static-exp '(+ 1 (* x 4)) '(() (x)))) ;#f

(define test_reduce1 '(mix-reduce '(+ 1 (* x 4)) '([x 3]))) ;13
(define test_reduce2 '(mix-reduce 'x '[(x '(1 2 3))]))
(define test_reduce3 '(mix-reduce '() '[]))
(define test_reduce4 '(mix-reduce '(list [list (caadr m0-program) m0-vs0]) '((m0-program '((read program Right) (main (:= Left '()) (:= cur (car Right)) (:= Right (cdr Right)) (:= progtail program) (goto next-instruction)))))))
(define test_reduce5 '(mix-reduce '(caadr m0-program) '((m0-program '((read program Right) (main (:= Left '()) (:= cur (car Right)) (:= Right (cdr Right)) (:= progtail program) (goto next-instruction)))))))
(define test_reduce6 '(mix-reduce '(list [cons some m0-vs0]) '((some 'main))))

(define tm-div '([program progtail inst instname next] [Right Left cur]));
(define mix0-div '([m0-bb m0-div m0-pp0 m0-program m0-blockcopy m0-blocks-in-pending m0-command m0-case m0-pps m0-ifexp m0-ifpp1 m0-ifpp2]
                   [m0-code m0-ppvs m0-residual m0-pending m0-marked m0-pp m0-vs m0-vs0]))

(define target0 `(run-mix0 find_name '([name namelist] [valuelist]) (hash 'name 'y 'namelist '(x y z))))
(define target1 `(run-mix0 int-tm tm-div (hash 'program tm-example)))
(define comp `(run-mix0 mix0 mix0-div (hash 'm0-program int-tm 'm0-div tm-div)))

(define check-tm2 '(int (eval target1) '(() (1 1 1 0 1 0 1))))
(define check-comp `(change-labels (int mix0-comp '(() () ([program ',tm-example])))))
(define check-comp2 '(int mix0-tm-compgen '(() (1 1 1 0 1 0 1))))

;=============================
;==== Auto-generated code ====
;=============================

(define tm-example-gen '((read program Right)
  ("main-0" 
  (:= Left '()) 
  (:= cur (car Right)) 
  (:= Right (cdr Right)) 
  (if (equal? 0 cur) "run-goto-2" "next-instruction-1"))
  ("next-instruction-1"
   (:= Left (cons cur Left))
   (:= cur (if (empty? Right) '() (car Right)))
   (:= Right (if (empty? Right) '() (cdr Right)))
   (if (equal? 0 cur) "run-goto-2" "next-instruction-1"))
  ("run-goto-2" (:= cur 1) (return (append `(,cur) Right)))))


(define mix0-tm-compgen '((read program Right)
  ("main-0"
   (:= Left '())
   (:= cur (car Right))
   (:= Right (cdr Right))
   (if (equal? 0 cur) "run-goto-2" "next-instruction-1"))
  ("next-instruction-1"
   (:= Left (cons cur Left))
   (:= cur (if (empty? Right) '() (car Right)))
   (:= Right (if (empty? Right) '() (cdr Right)))
   (if (equal? 0 cur) "run-goto-2" "next-instruction-1"))
  ("run-goto-2" (:= cur 1) (return (append `(,cur) Right)))))

(define mix0-comp '((read m0-program m0-div m0-vs0)
("mix0-main-0"
		(:= m0-pending (set (list "main" m0-vs0)))
		(:= m0-marked (set))
		(:= m0-residual (quote ((read program Right))))
		(if (set-empty? m0-pending) "mix0-end-1" "mix0-cont1-2"))
("mix0-end-1"
		(return (reverse m0-residual)))
("mix0-cont1-2"
		(:= m0-ppvs (set-first m0-pending))
		(:= m0-pp (car m0-ppvs))
		(:= m0-vs (cadr m0-ppvs))
		(:= m0-pending (set-rest m0-pending))
		(:= m0-marked (set-add m0-marked m0-ppvs))
		(:= m0-code (list m0-ppvs))
		(if (equal? m0-pp "main") "mix0-foundpp-3" "mix0-notfoundpp-69"))
("mix0-foundpp-3"
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote (quote ())) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote (car Right)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote (cdr Right)) m0-vs)) m0-code))
		(:= m0-vs (int-assign progtail program m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-5" "mix0-if-false-4"))
("mix0-if-false-4"
		(:= m0-vs (int-assign inst (quote (car progtail)) m0-vs))
		(:= m0-vs (int-assign instname (quote (cadr inst)) m0-vs))
		(:= m0-vs (int-assign progtail (quote (cdr progtail)) m0-vs))
		(if (int-eval m0-vs (quote (equal? instname (quote left)))) "mix0-if-true-81" "mix0-if-false-9"))
("mix0-if-true-5"
		(:= m0-code (cons (list (quote return) (mix-reduce (quote (append (quasiquote ((unquote cur))) Right)) m0-vs)) m0-code))
		(:= m0-residual (cons (reverse m0-code) m0-residual))
		(if (set-empty? m0-pending) "mix0-end-11" "mix0-cont1-6"))
("mix0-cont1-6"
		(:= m0-ppvs (set-first m0-pending))
		(:= m0-pp (car m0-ppvs))
		(:= m0-vs (cadr m0-ppvs))
		(:= m0-pending (set-rest m0-pending))
		(:= m0-marked (set-add m0-marked m0-ppvs))
		(:= m0-code (list m0-ppvs))
		(if (equal? m0-pp "main") "mix0-foundpp-8" "mix0-notfoundpp-7"))
("mix0-notfoundpp-7"
		(return "lookup error"))
("mix0-foundpp-8"
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote (quote ())) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote (car Right)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote (cdr Right)) m0-vs)) m0-code))
		(:= m0-vs (int-assign progtail program m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-5" "mix0-if-false-4"))
("mix0-if-false-9"
		(if (int-eval m0-vs (quote (equal? instname (quote right)))) "mix0-if-true-10" "mix0-if-false-12"))
("mix0-if-true-10"
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote (cons cur Left)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote
		(if (empty? Right) (quote ()) (car Right))) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote
		(if (empty? Right) (quote ()) (cdr Right))) m0-vs)) m0-code))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-5" "mix0-if-false-4"))
("mix0-end-11"
		(return (reverse m0-residual)))
("mix0-if-false-12"
		(if (int-eval m0-vs (quote (equal? instname (quote write)))) "mix0-if-true-15" "mix0-if-false-13"))
("mix0-if-false-13"
		(if (int-eval m0-vs (quote (equal? instname (quote goto)))) "mix0-if-true-16" "mix0-if-false-14"))
("mix0-if-false-14"
		(if (int-eval m0-vs (quote (equal? instname (quote if)))) "mix0-if-true-17" "mix0-if-false-83"))
("mix0-if-true-15"
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote (caddr inst)) m0-vs)) m0-code))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-5" "mix0-if-false-4"))
("mix0-if-true-16"
		(:= m0-vs (int-assign next (quote (caddr inst)) m0-vs))
		(:= m0-vs (int-assign progtail (quote (tm-goto next program)) m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-5" "mix0-if-false-4"))
("mix0-if-true-17"
		(:= m0-vs (int-assign next (quote (last inst)) m0-vs))
		(:= m0-pending (set-union m0-pending (set-subtract (set (list "run-goto" m0-vs) (list "next-instruction" m0-vs)) m0-marked)))
		(:= m0-code (cons (list (quote if) (mix-reduce (quote (equal? (caddr inst) cur)) m0-vs) (list "run-goto" m0-vs) (list "next-instruction" m0-vs)) m0-code))
		(:= m0-residual (cons (reverse m0-code) m0-residual))
		(if (set-empty? m0-pending) "mix0-end-71" "mix0-cont1-18"))
("mix0-cont1-18"
		(:= m0-ppvs (set-first m0-pending))
		(:= m0-pp (car m0-ppvs))
		(:= m0-vs (cadr m0-ppvs))
		(:= m0-pending (set-rest m0-pending))
		(:= m0-marked (set-add m0-marked m0-ppvs))
		(:= m0-code (list m0-ppvs))
		(if (equal? m0-pp "next-instruction") "mix0-foundpp-43" "mix0-notfoundpp-19"))
("mix0-notfoundpp-19"
		(if (equal? m0-pp "run-goto") "mix0-foundpp-22" "mix0-notfoundpp-20"))
("mix0-notfoundpp-20"
		(if (equal? m0-pp "main") "mix0-foundpp-44" "mix0-notfoundpp-21"))
("mix0-notfoundpp-21"
		(return "lookup error"))
("mix0-foundpp-22"
		(:= m0-vs (int-assign progtail (quote (tm-goto next program)) m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-27" "mix0-if-false-23"))
("mix0-if-false-23"
		(:= m0-vs (int-assign inst (quote (car progtail)) m0-vs))
		(:= m0-vs (int-assign instname (quote (cadr inst)) m0-vs))
		(:= m0-vs (int-assign progtail (quote (cdr progtail)) m0-vs))
		(if (int-eval m0-vs (quote (equal? instname (quote left)))) "mix0-if-true-61" "mix0-if-false-24"))
("mix0-if-false-24"
		(if (int-eval m0-vs (quote (equal? instname (quote right)))) "mix0-if-true-25" "mix0-if-false-26"))
("mix0-if-true-25"
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote (cons cur Left)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote
		(if (empty? Right) (quote ()) (car Right))) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote
		(if (empty? Right) (quote ()) (cdr Right))) m0-vs)) m0-code))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-27" "mix0-if-false-23"))
("mix0-if-false-26"
		(if (int-eval m0-vs (quote (equal? instname (quote write)))) "mix0-if-true-65" "mix0-if-false-88"))
("mix0-if-true-27"
		(:= m0-code (cons (list (quote return) (mix-reduce (quote (append (quasiquote ((unquote cur))) Right)) m0-vs)) m0-code))
		(:= m0-residual (cons (reverse m0-code) m0-residual))
		(if (set-empty? m0-pending) "mix0-end-28" "mix0-cont1-29"))
("mix0-end-28"		(return (reverse m0-residual)))
("mix0-cont1-29"
		(:= m0-ppvs (set-first m0-pending))
		(:= m0-pp (car m0-ppvs))
		(:= m0-vs (cadr m0-ppvs))
		(:= m0-pending (set-rest m0-pending))
		(:= m0-marked (set-add m0-marked m0-ppvs))
		(:= m0-code (list m0-ppvs))
		(if (equal? m0-pp "next-instruction") "mix0-foundpp-33" "mix0-notfoundpp-30"))
("mix0-notfoundpp-30"		(if (equal? m0-pp "run-goto") "mix0-foundpp-42" "mix0-notfoundpp-31"))
("mix0-notfoundpp-31"		(if (equal? m0-pp "main") "mix0-foundpp-68" "mix0-notfoundpp-32"))
("mix0-notfoundpp-32"		(return "lookup error"))
("mix0-foundpp-33"
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-34" "mix0-if-false-36"))
("mix0-if-true-34"
		(:= m0-code (cons (list (quote return) (mix-reduce (quote (append (quasiquote ((unquote cur))) Right)) m0-vs)) m0-code))
		(:= m0-residual (cons (reverse m0-code) m0-residual))
		(if (set-empty? m0-pending) "mix0-end-35" "mix0-cont1-39"))
("mix0-end-35"
		(return (reverse m0-residual)))
("mix0-if-false-36"
		(:= m0-vs (int-assign inst (quote (car progtail)) m0-vs))
		(:= m0-vs (int-assign instname (quote (cadr inst)) m0-vs))
		(:= m0-vs (int-assign progtail (quote (cdr progtail)) m0-vs))
		(if (int-eval m0-vs (quote (equal? instname (quote left)))) "mix0-if-true-40" "mix0-if-false-37"))
("mix0-if-false-37"
		(if (int-eval m0-vs (quote (equal? instname (quote right)))) "mix0-if-true-70" "mix0-if-false-38"))
("mix0-if-false-38"
		(if (int-eval m0-vs (quote (equal? instname (quote write)))) "mix0-if-true-41" "mix0-if-false-72"))
("mix0-cont1-39"
		(:= m0-ppvs (set-first m0-pending))
		(:= m0-pp (car m0-ppvs))
		(:= m0-vs (cadr m0-ppvs))
		(:= m0-pending (set-rest m0-pending))
		(:= m0-marked (set-add m0-marked m0-ppvs))
		(:= m0-code (list m0-ppvs))
		(if (equal? m0-pp "next-instruction") "mix0-foundpp-33" "mix0-notfoundpp-30"))
("mix0-if-true-40"
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote (cons cur Right)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote
		(if (empty? Left) (quote ()) (car Left))) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote
		(if (empty? Left) (quote ()) (cdr Left))) m0-vs)) m0-code))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-34" "mix0-if-false-36"))
("mix0-if-true-41"
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote (caddr inst)) m0-vs)) m0-code))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-34" "mix0-if-false-36"))
("mix0-foundpp-42"
		(:= m0-vs (int-assign progtail (quote (tm-goto next program)) m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-27" "mix0-if-false-23"))
("mix0-foundpp-43"
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-34" "mix0-if-false-36"))
("mix0-foundpp-44"
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote (quote ())) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote (car Right)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote (cdr Right)) m0-vs)) m0-code))
		(:= m0-vs (int-assign progtail program m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-45" "mix0-if-false-46"))
("mix0-if-true-45"
		(:= m0-code (cons (list (quote return) (mix-reduce (quote (append (quasiquote ((unquote cur))) Right)) m0-vs)) m0-code))
		(:= m0-residual (cons (reverse m0-code) m0-residual))
		(if (set-empty? m0-pending) "mix0-end-54" "mix0-cont1-59"))
("mix0-if-false-46"
		(:= m0-vs (int-assign inst (quote (car progtail)) m0-vs))
		(:= m0-vs (int-assign instname (quote (cadr inst)) m0-vs))
		(:= m0-vs (int-assign progtail (quote (cdr progtail)) m0-vs))
		(if (int-eval m0-vs (quote (equal? instname (quote left)))) "mix0-if-true-60" "mix0-if-false-47"))
("mix0-if-false-47"
		(if (int-eval m0-vs (quote (equal? instname (quote right)))) "mix0-if-true-48" "mix0-if-false-49"))
("mix0-if-true-48"
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote (cons cur Left)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote
		(if (empty? Right) (quote ()) (car Right))) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote
		(if (empty? Right) (quote ()) (cdr Right))) m0-vs)) m0-code))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-45" "mix0-if-false-46"))
("mix0-if-false-49"
		(if (int-eval m0-vs (quote (equal? instname (quote write)))) "mix0-if-true-66" "mix0-if-false-50"))
("mix0-if-false-50"
		(if (int-eval m0-vs (quote (equal? instname (quote goto)))) "mix0-if-true-52" "mix0-if-false-51"))
("mix0-if-false-51"
		(if (int-eval m0-vs (quote (equal? instname (quote if)))) "mix0-if-true-53" "mix0-if-false-55"))
("mix0-if-true-52"
		(:= m0-vs (int-assign next (quote (caddr inst)) m0-vs))
		(:= m0-vs (int-assign progtail (quote (tm-goto next program)) m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-45" "mix0-if-false-46"))
("mix0-if-true-53"
		(:= m0-vs (int-assign next (quote (last inst)) m0-vs))
		(:= m0-pending (set-union m0-pending (set-subtract (set (list "run-goto" m0-vs) (list "next-instruction" m0-vs)) m0-marked)))
		(:= m0-code (cons (list (quote if) (mix-reduce (quote (equal? (caddr inst) cur)) m0-vs) (list "run-goto" m0-vs) (list "next-instruction" m0-vs)) m0-code))
		(:= m0-residual (cons (reverse m0-code) m0-residual))
		(if (set-empty? m0-pending) "mix0-end-71" "mix0-cont1-18"))
("mix0-end-54"
		(return (reverse m0-residual)))
("mix0-if-false-55"
		(:= m0-code (cons (list (quote return) (mix-reduce (quote (string-append mismatch with  (~a instname))) m0-vs)) m0-code))
		(:= m0-residual (cons (reverse m0-code) m0-residual))
		(if (set-empty? m0-pending) "mix0-end-67" "mix0-cont1-56"))
("mix0-cont1-56"
		(:= m0-ppvs (set-first m0-pending))
		(:= m0-pp (car m0-ppvs))
		(:= m0-vs (cadr m0-ppvs))
		(:= m0-pending (set-rest m0-pending))
		(:= m0-marked (set-add m0-marked m0-ppvs))
		(:= m0-code (list m0-ppvs))
		(if (equal? m0-pp "next-instruction") "mix0-foundpp-58" "mix0-notfoundpp-57"))
("mix0-notfoundpp-57"
		(if (equal? m0-pp "run-goto") "mix0-foundpp-82" "mix0-notfoundpp-62"))
("mix0-foundpp-58"
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-34" "mix0-if-false-36"))
("mix0-cont1-59"
		(:= m0-ppvs (set-first m0-pending))
		(:= m0-pp (car m0-ppvs))
		(:= m0-vs (cadr m0-ppvs))
		(:= m0-pending (set-rest m0-pending))
		(:= m0-marked (set-add m0-marked m0-ppvs))
		(:= m0-code (list m0-ppvs))
		(if (equal? m0-pp "next-instruction") "mix0-foundpp-33" "mix0-notfoundpp-30"))
("mix0-if-true-60"
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote (cons cur Right)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote
		(if (empty? Left) (quote ()) (car Left))) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote
		(if (empty? Left) (quote ()) (cdr Left))) m0-vs)) m0-code))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-45" "mix0-if-false-46"))
("mix0-if-true-61"
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote (cons cur Right)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote
		(if (empty? Left) (quote ()) (car Left))) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote
		(if (empty? Left) (quote ()) (cdr Left))) m0-vs)) m0-code))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-27" "mix0-if-false-23"))
("mix0-notfoundpp-62"
		(if (equal? m0-pp "main") "mix0-foundpp-63" "mix0-notfoundpp-64"))
("mix0-foundpp-63"
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote (quote ())) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote (car Right)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote (cdr Right)) m0-vs)) m0-code))
		(:= m0-vs (int-assign progtail program m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-45" "mix0-if-false-46"))
("mix0-notfoundpp-64"
		(return "lookup error"))
("mix0-if-true-65"
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote (caddr inst)) m0-vs)) m0-code))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-27" "mix0-if-false-23"))
("mix0-if-true-66"
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote (caddr inst)) m0-vs)) m0-code))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-45" "mix0-if-false-46"))
("mix0-end-67"
		(return (reverse m0-residual)))
("mix0-foundpp-68"
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote (quote ())) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote (car Right)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote (cdr Right)) m0-vs)) m0-code))
		(:= m0-vs (int-assign progtail program m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-45" "mix0-if-false-46"))
("mix0-notfoundpp-69"
		(return "lookup error"))
("mix0-if-true-70"
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote (cons cur Left)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote
		(if (empty? Right) (quote ()) (car Right))) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote
		(if (empty? Right) (quote ()) (cdr Right))) m0-vs)) m0-code))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-34" "mix0-if-false-36"))
("mix0-end-71"
		(return (reverse m0-residual)))
("mix0-if-false-72"
		(if (int-eval m0-vs (quote (equal? instname (quote goto)))) "mix0-if-true-76" "mix0-if-false-73"))
("mix0-if-false-73"
		(if (int-eval m0-vs (quote (equal? instname (quote if)))) "mix0-if-true-78" "mix0-if-false-74"))
("mix0-if-false-74"
		(:= m0-code (cons (list (quote return) (mix-reduce (quote (string-append mismatch with  (~a instname))) m0-vs)) m0-code))
		(:= m0-residual (cons (reverse m0-code) m0-residual))
		(if (set-empty? m0-pending) "mix0-end-75" "mix0-cont1-77"))
("mix0-end-75"
		(return (reverse m0-residual)))
("mix0-if-true-76"
		(:= m0-vs (int-assign next (quote (caddr inst)) m0-vs))
		(:= m0-vs (int-assign progtail (quote (tm-goto next program)) m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-34" "mix0-if-false-36"))
("mix0-cont1-77"
		(:= m0-ppvs (set-first m0-pending))
		(:= m0-pp (car m0-ppvs))
		(:= m0-vs (cadr m0-ppvs))
		(:= m0-pending (set-rest m0-pending))
		(:= m0-marked (set-add m0-marked m0-ppvs))
		(:= m0-code (list m0-ppvs))
		(if (equal? m0-pp "next-instruction") "mix0-foundpp-58" "mix0-notfoundpp-57"))
("mix0-if-true-78"
		(:= m0-vs (int-assign next (quote (last inst)) m0-vs))
		(:= m0-pending (set-union m0-pending (set-subtract (set (list "run-goto" m0-vs) (list "next-instruction" m0-vs)) m0-marked)))
		(:= m0-code (cons (list (quote if) (mix-reduce (quote (equal? (caddr inst) cur)) m0-vs) (list "run-goto" m0-vs) (list "next-instruction" m0-vs)) m0-code))
		(:= m0-residual (cons (reverse m0-code) m0-residual))
		(if (set-empty? m0-pending) "mix0-end-79" "mix0-cont1-80"))
("mix0-end-79"
		(return (reverse m0-residual)))
("mix0-cont1-80"
		(:= m0-ppvs (set-first m0-pending))
		(:= m0-pp (car m0-ppvs))
		(:= m0-vs (cadr m0-ppvs))
		(:= m0-pending (set-rest m0-pending))
		(:= m0-marked (set-add m0-marked m0-ppvs))
		(:= m0-code (list m0-ppvs))
		(if (equal? m0-pp "next-instruction") "mix0-foundpp-43" "mix0-notfoundpp-19"))
("mix0-if-true-81"
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote (cons cur Right)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote
		(if (empty? Left) (quote ()) (car Left))) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote
		(if (empty? Left) (quote ()) (cdr Left))) m0-vs)) m0-code))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-5" "mix0-if-false-4"))
("mix0-foundpp-82"
		(:= m0-vs (int-assign progtail (quote (tm-goto next program)) m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-27" "mix0-if-false-23"))
("mix0-if-false-83"
		(:= m0-code (cons (list (quote return) (mix-reduce (quote (string-append mismatch with  (~a instname))) m0-vs)) m0-code))
		(:= m0-residual (cons (reverse m0-code) m0-residual))
		(if (set-empty? m0-pending) "mix0-end-84" "mix0-cont1-85"))
("mix0-end-84"
		(return (reverse m0-residual)))
("mix0-cont1-85"
		(:= m0-ppvs (set-first m0-pending))
		(:= m0-pp (car m0-ppvs))
		(:= m0-vs (cadr m0-ppvs))
		(:= m0-pending (set-rest m0-pending))
		(:= m0-marked (set-add m0-marked m0-ppvs))
		(:= m0-code (list m0-ppvs))
		(if (equal? m0-pp "main") "mix0-foundpp-86" "mix0-notfoundpp-87"))
("mix0-foundpp-86"
		(:= m0-code (cons (list (quote :=) Left (mix-reduce (quote (quote ())) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) cur (mix-reduce (quote (car Right)) m0-vs)) m0-code))
		(:= m0-code (cons (list (quote :=) Right (mix-reduce (quote (cdr Right)) m0-vs)) m0-code))
		(:= m0-vs (int-assign progtail program m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-5" "mix0-if-false-4"))
("mix0-notfoundpp-87"
		(return "lookup error"))
("mix0-if-false-88"
		(if (int-eval m0-vs (quote (equal? instname (quote goto)))) "mix0-if-true-92" "mix0-if-false-89"))
("mix0-if-false-89"
		(if (int-eval m0-vs (quote (equal? instname (quote if)))) "mix0-if-true-90" "mix0-if-false-94"))
("mix0-if-true-90"
		(:= m0-vs (int-assign next (quote (last inst)) m0-vs))
		(:= m0-pending (set-union m0-pending (set-subtract (set (list "run-goto" m0-vs) (list "next-instruction" m0-vs)) m0-marked)))
		(:= m0-code (cons (list (quote if) (mix-reduce (quote (equal? (caddr inst) cur)) m0-vs) (list "run-goto" m0-vs) (list "next-instruction" m0-vs)) m0-code))
		(:= m0-residual (cons (reverse m0-code) m0-residual))
		(if (set-empty? m0-pending) "mix0-end-93" "mix0-cont1-91"))
("mix0-cont1-91"
		(:= m0-ppvs (set-first m0-pending))
		(:= m0-pp (car m0-ppvs))
		(:= m0-vs (cadr m0-ppvs))
		(:= m0-pending (set-rest m0-pending))
		(:= m0-marked (set-add m0-marked m0-ppvs))
		(:= m0-code (list m0-ppvs))
		(if (equal? m0-pp "next-instruction") "mix0-foundpp-43" "mix0-notfoundpp-19"))
("mix0-if-true-92"
		(:= m0-vs (int-assign next (quote (caddr inst)) m0-vs))
		(:= m0-vs (int-assign progtail (quote (tm-goto next program)) m0-vs))
		(if (int-eval m0-vs (quote (empty? progtail))) "mix0-if-true-27" "mix0-if-false-23"))
("mix0-end-93"м
		(return (reverse m0-residual)))
("mix0-if-false-94"
		(:= m0-code (cons (list (quote return) (mix-reduce (quote (string-append mismatch with  (~a instname))) m0-vs)) m0-code))
		(:= m0-residual (cons (reverse m0-code) m0-residual))
		(if (set-empty? m0-pending) "mix0-end-95" "mix0-cont1-96"))
("mix0-end-95"
		(return (reverse m0-residual)))
("mix0-cont1-96"
		(:= m0-ppvs (set-first m0-pending))
		(:= m0-pp (car m0-ppvs))
		(:= m0-vs (cadr m0-ppvs))
		(:= m0-pending (set-rest m0-pending))
		(:= m0-marked (set-add m0-marked m0-ppvs))
		(:= m0-code (list m0-ppvs))
		(if (equal? m0-pp "next-instruction") "mix0-foundpp-58" "mix0-notfoundpp-57"))))

;=======================
;==== change labels ====
;=======================

(define (fl-pretty-print program)
  (match program
    ['() (printf "\n")]
    [(cons x xs) (printf "~s\n" x)
                 (fl-pretty-print xs)]))
 
(define (get-labels prog)
  (let ([prog (cdr prog)])
    (map (lambda (x i) (cons (car x) (string-append [~a (caar x)] "-" (number->string i)))) prog (build-list (length prog) values))))
 
(define (change-labels prog)
  (let ([mapping (get-labels prog)])
    (for/list ([el prog]) (map-labels el mapping))))
 
(define (map-labels x mapping)
  (cond ((dict-has-key? mapping x) (dict-ref mapping x))
        ((list? x) (map (lambda (y) (map-labels y mapping)) x))
        (else x)))

(define-namespace-anchor anc)
(define ns (namespace-anchor->namespace anc))

;(displayln (eval comp ns))
