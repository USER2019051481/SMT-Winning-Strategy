(define (domain Subtraction_game-2-3)
	(:objects ?v1)
	(:tercondition (and (>= ?v1 0) (< ?v1 2) ))
	(:constraint (>= ?v1 0))
	(:action take
		:parameters (?k)
		:precondition (and (>= ?v1 ?k) (or (= ?k 2) (= ?k 3) (= ?k 8)))
		:effect (assign ?v1 (- ?v1 ?k)))
)