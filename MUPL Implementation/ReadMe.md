# MUPL Implementation
This project serves as a daily reminder on how code are compiled and evaluated under the hood, in particular:
- Let-expression effect on environment
- Function evaluation
- Variable bindings
- Macros
- If-else statement

And especially the environment's role in evaluating expression.

To run correctly, create your own MUPL expression and evaluate it with (eval-exp **MUPL-expression**).

Here are some test you can try yourself:
- (eval-exp (call (call mupl-all-gt (int 5)) (apair (int 4) (apair (int 7) (apair (int 3) (apair (int 9) (munit)))))))
- (eval-under-env-c (compute-free-vars (call (call mupl-all-gt (int 5)) (apair (int 4) (apair (int 7) (apair (int 3) (apair (int 9) (munit))))))) (list (cons "x" (int 42)) (cons "y" (int 33)) (cons "HUH" (int 77))))

The first test utilize a naive approach to evaluating MUPL, where building closure are done under the **main** environment. The second test employ a smarter approach where building closure are done in a much smaller environment, consists of only free variables found in the functions. 
- **Definition:** Free variables are those not bounded by anything. i.e. (fun "add-y" "x" (add (var "x") (var "y"))) where "y" is a free variable as it is unknown should the environment be null, whereas "x" is the function argument, and will natural be known when the function is called.
