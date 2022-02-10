# Automated Robustness Verification
We present some additional information in this file to explain concepts in the
paper in further detail.

## Encoding execution graphs using SMT
Our verification approach relies on using execution graphs to represent
program executions. We search for the existence of a robustness violating
witness in these executions graphs using SMT solvers which denotes that the
program is not robust. The absence of any such witness denotes that the
program is robust. In the following paragraphs, we explain the salient
features of our encoding.

We use uninterpreted sorts to represent events, values, invocations and
sessions. Constants of sort `E` are used to represent events. Other
constants are used to denote constraints on values, invocations and
sessions.

```smt2
(declare-sort E) ; Sort for events
(declare-sort V) ; Sort for values
(declare-sort S) ; Sort for sessions

(declare-sort I) ; Sort for invocations
```

We use some inductive datatypes to ascribe information to each event such
as the location accessed, value accessed and access type -

```
(declare-datatypes () ((EventType R W U F)))              ; Type of access
(declare-datatypes () ((EventLabel Rlx Rel Acq AcqRel)))  ; Access memory order
(declare-datatypes () ((Field Default Val Next)))         ; Access location 
```

We then define uninterpreted functions which are used to ascribe information
to each event. Some examples of such functions, which denote the type and
memory order of each event are as follows -

```smt2
(declare-fun etype  (E) EventType)  ; Mapping every event to its access type
(declare-fun elabel (E) EventLabel) ; Mapping every event to its memory order
```

Finally, we use binary predicates to encode the relations which denote an
exeuction graph -

```smt2
(declare-fun so   (E E) Bool) ; session order
(declare-fun rf   (E E) Bool) ; reads from 
(declare-fun mo   (E E) Bool) ; memory order
(declare-fun sw   (E E) Bool) ; synchronizes with
(declare-fun fr   (E E) Bool) ; from reads
(declare-fun hb   (E E) Bool) ; happens before
(declare-fun hbSC (E E) Bool) ; happens before (sequential consistency)
```

For each relation, we also declare the constraints necessary. For example, the
`mo` relation should be a total order for all locations -

```smt2
(assert (forall ((e1 E) (e2 E)) ; for all events e1, e2
  (=> (mo e1 e2)                ; mo e1 e2 implies 
      (not (mo e2 e1))))        ; not (mo e2 e1)

(assert (forall ((e1 E) (e2 E) (e3 E)) ; for all events e1, e2, e3
  (=> (and (mo e1 e2) (mo e2 e3))      ; (mo e1 e2) and (mo e2 e3) implies
      (mo e1 e3))))                    ; (mo e1 e3)
```

We also have additional constraints for each relation consistent with our
implementation such as reads-from should relate a read and a write or that
session order should exist between all events in a particular session.

After this, we introduce the encoding of invocations. An invocation represents
a single call to a library method by a client in a particular session with 
some arguments and a return value as follows -

```
(declare-datatypes Method ((Enq Deq)))  ; datatypes for invocation labels
(declare-fun sess   (I) S)              ; function mapping invocation to session
(declare-fun argval (I) S)              ; function mapping invocation to argument value
(declare-fun retval (I) S)              ; function mapping invocation to return value
(declare-fun itype  (I) Method)         ; function mapping invocation to method label
```

Each event is mapped to an invocation through functions. For example, the
following functions are used to denote the 4 events that make up a certain
invocation -

```
(declare-fun E1e (I) E)
(declare-fun E2e (I) E)
(declare-fun E3e (I) E)
(declare-fun E4e (I) E)
```

We also have a function which maps the linerization point of a function
to an event - 

```
(declare-fun LP (I) E)
```

Finally, the linearizability axioms are specified in the form of relations
between invocations. For example, the AddRem axiom is specified as -

```
(declare-fun matchm (I I) Bool)                            ; utility function for use in axioms
(assert (forall ((i1 I) (i2 I))
                (= (matchm i1 i2)
                   (and 
                     (= (itype i1) Enq)
                     (= (itype i2) Deq)
                     (= (argval i1) (retval i2))))))

(assert (forall ((i1 I) (i2 I))
                (=> (matchm i1 i2) (hb (LP i1) (LP i2))))) ; AddRem axiom
```

Given this SMT encoding, a satisfiable model for this instance of formulas
represents a possible program execution. Further, it becomes possible to pose
the following robustness query for a given exeuction graph, where `e1` and `e2`
are instantiated to specific events - 

```smt2
(assert (=> (hbSC e1 e2) (not hb e1 e2)))
```

## Detailed explanation of Treiber stack
We first present the code for a Treiber stack implementation that we have
considered for verification. This library implementation has two methods
as follows -

```c
void push(int v) {
  node* n = malloc(sizeof(node)); 
  atomic_store_explicit(&(n->val), v , memory_order_relaxed);
  while(true) {
    node* t = atomic_load_explicit(top, memory_order_relaxed);
    atomic_store_explicit(&(n->next), t, memory_order_relaxed);
    if (atomic_compare_exchange_strong_explicit(top, t, n, memory_order_acqrel)) // LP, push
      break;
  }
}

int pop() {
  while(true) {
    node* t = atomic_load_explicit(top, memory_order_acquire); // LP, pop
    if (t == NULL)
      return EMPTY;
    int v = atomic_load_explicit(&(t->val), memory_order_relaxed);
    node* n = atomic_load_explicit(&(t->next), memory_order_relaxed);
    if(atomic_compare_exchange_string_explicit(top, t, n, memory_order_acqrel)) // LP, pop
      return v;
  }
}
```

The comments of the form `LP, push` and `LP, pop` denote that these points are
linearization points corresponding to a certain method. Given that these
linearization points can be non-local to a given method, the method annotation
allows us to track the method to which the linearization point belongs.

Along with this, the user provides the linearizability specification of the
following form. We parse this formula to then generate the necessary
hb-constraints.

```
forall (i1 i2 : I), method(i1) == POP & retval(i1) != NULL => method(i2) == PUSH & retval(i1) == argval(i2)
forall (i1 i2 i3 : I), method(i3) == POP & retval(i3) == NULL => method(i1) == PUSH & method(i2) == POP & argval(i1) == argval(i2)
```

Given that the CAS operations can arbitrarily fail, these methods would
generate an infinite number of events. Our tool first performs a
robustness-preserving transformation that allows us to reason about the
behavior of these methods using a finite number of events. The transformed
program is as follows -

```c
void push(int v) {
  node* n = malloc(sizeof(node));
  atomic_store_explicit(&(n->val), v , memory_order_relaxed); // E1e
  node* t = atomic_load_explicit(top, memory_order_relaxed);  // E2e
  atomic_store_explicit(&(n->next), t, memory_order_relaxed); // E3e
  bcas_explicit(top, t, n, memory_order_acqrel);              // E4e
}

int pop() {
  node* t = atomic_load_explicit(top, memory_order_acquire);        // D1e
  if (t == NULL)
    return EMPTY;
  int v = atomic_load_explicit(&(t->val), memory_order_relaxed);    // D2e
  node* n = atomic_load_explicit(&(t->next), memory_order_relaxed); // D3e
  bcas_explicit(top, t, n, memory_order_acqrel);                    // D4e
  return v;
}
```

Notice that we have replaced the CASs with blocking CAS operations which we
denote as `bcas_explicit` in the code. This removes the while loop, as the
`bcas` operation means that the CAS blocks until it succeeds, thus removing
the need for a retry loop. This relies on the assumption that the failing
CAS events do not have any visible effects, thus can be ignored. We have also
labelled each line of code with its corresponding event label.

After this transformation, we perform a syntactical analysis to gather the
locations accessed by a library implementation. This analysis will
parse the library code and traverse the AST, returning the set of locations
accssed. In this case, it will return - 

* `top`
* `n->next`
* `n->val`

Further, the access constraint pre-processing step will generate the constraint
that there is always a unique write to `val` thus, a read to `val` will always
return the initialization value. Once this is done, the events corresponding
to each memory operation are generated. First we show the memory events
generated for the push method -

```smt
(assert (forall ((i I)) (=> (= (itype i) Enq) (and (= (etype (E1e i)) W) (= (elabel (E1e i)) Rlx)  (= (loc (E1e i)) (newloc i)) (= (stype (E1e i)) E1t) (= (field (E1e i)) Val) (= (wval (E1e i)) (argval i)) (= (valevent i) (E1e i))))))

(assert (forall ((i I)) (=> (= (itype i) Enq) (and (= (etype (E2e i)) R) (= (elabel (E2e i)) Rlx)  (= (loc (E2e i)) head) (= (stype (E2e i)) E2t) (= (field (E2e i)) Default) (= (rval (E2e i)) (enqh i))))))

(assert (forall ((i I)) (=> (= (itype i) Enq) (and (= (etype (E3e i)) W) (= (elabel (E3e i)) Rlx)  (= (loc (E3e i)) (newloc i)) (= (stype (E3e i)) E3t) (= (field (E3e i)) Next) (= (wval (E3e i)) (enqh i))))))

(assert (forall ((i I)) (=> (= (itype i) Enq) (and (= (etype (E4e i)) U) (= (elabel (E4e i)) AcqRel)  (= (loc (E4e i)) head) (= (stype (E4e i)) E4t) (= (field (E4e i)) Default) (= (rval (E4e i)) (enqh i)) (= (wval (E4e i)) (newloc i))))))
```

Then we show the memory events corresponding to the pop method -

```smt
(assert (forall ((i I)) (=> (= (itype i) Deq) (and (= (rval (D1e i)) (deqh i)) (= (loc (D1e i)) top) (= (field (D1e i)) Default) (= (etype (D1e i)) R) (= (elabel (D1e i)) Acq)))))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (= (deqh i) NULL)) (and (= (retval i) EMPTY) (isBot (D2e i)) (isBot (D3e i)) (isBot (D4e i))))))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (not (= (deqh i) NULL))) (and (= (rval (D2e i)) (deqv i)) (= (stype (D2e i)) D2t) (= (loc (D2e i)) (deqh i)) (= (field (D2e i)) Val) (= (etype (D2e i)) R) (= (elabel (D2e i)) Rlx)))))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (not (= (deqh i) NULL))) (and (= (rval (D3e i)) (deqn i)) (= (stype (D3e i)) D3t) (= (loc (D3e i)) (deqh i)) (= (field (D3e i)) Next) (= (etype (D3e i)) R) (= (elabel (D3e i)) Rlx)))))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (not (= (deqh i) NULL))) (and (= (retval i) (deqv i)) (= (rval (D4e i)) (deqh i)) (= (wval (D4e i)) (deqn i)) (= (stype (D4e i)) D4t) (= (loc (D4e i)) head) (= (field (D4e i)) Default) (= (etype (D4e i)) U) (= (elabel (D4e i)) AcqRel)))))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (not (= (deqh i) NULL))) (and (not (= (retval i) EMPTY)) (not (= (retval i) zero))))))
```

Our verification algorithm proceeds by checking every pair of locations that
can generate a non-robust witness. Given that there are 3 location classes in
the Treiber Stack namely - `Top`, `Next` and `Val`, we have the following set
of cases that we need to verify.

| Case | L   | L'  |
|------|-----|-----|
|   1  | Top | Top |
|   2  | Top | Next|
|   3  | Top | Val |
|   4  | Next| Top |
|   5  | Next| Next|
|   6  | Next| Val |
|   7  | Val | Top |
|   8  | Val | Next|
|   9  | Val | Val |

We detail the SMT query for one case here -

```smt
; linearizability point axiom encoding
(assert (forall ((i1 I) (i2 I)) (=> (matchm i1 i2)  (hb (E4e i1) (D1e i2)))))

; Encoding hbSC but non-hb path between R(N.Next) and W(N.Next).
; UNSAT means that there cannot exist such events
(assert (= (itype in1) Deq ))
(assert (= (itype in2) Enq ))
(assert (rf (E3e in2) (D3e in1))) ; events instantiated to wmax and next e
(assert (not (hb (E3e in2) (D3e in1))))
```

Thus as this query returns UNSAT, it can be show that no such path exists. We
perform the remaining queries in an automated fashion for each pair of location
and edge pair.

## Detailed explanation of Lock-free queue
We verify the following code for the Michael-Scott non-blocking queue -

```c
void enq(int v) {
  while(true) {
    node* n = malloc(sizeof(node));
    atomic_store_explicit(&(n->val), v, memory_order_relaxed);
    node* t = atomic_load_explicit(tail, memory_order_acquire);
    node* next = atomic_load_explicit(&(tail->next), memory_order_acquire);
    
    if(next == NULL) {
      if(atomic_compare_exchange_strong(&(t->next), next, n, memory_order_acqrel)) // LP, enq
        atomic_compare_exchange_strong(tail, t, next, memory_order_acqrel);
      }
      break;
    }

    else { 
      atomic_compare_exchange_strong(tail, t, next, memory_order_acqrel);
    }
  }
}

int deq() {
  while(true) {
    node* h = atomic_load_explicit(head, memory_order_acquire);
    node* t = atomic_load_explicit(tail, memory_order_acquire);
    node* n = atomic_load_explicit(&(head->next), memory_order_relaxed);  // LP, deq

    if (n == NULL) {
      return NULL;
    }

    if (h == l) {
      atomic_compare_exchange_strong(tail, t, n, memory_order_acqrel);
      continue;
    }

    int r = atomic_load_explicit(&(n->val), memory_order_relaxed);
    if(atomic_compare_exchange_strong(head, h, n, memory_order_acqrel)) { // LP, deq
      break;
    }
  }

  return r;
}
```

The comments of the form `LP, deq` and `LP, enq` represent the linearization
points provided by the user. In this benchmark, note that enqueue calls which
do not add a new node but just move tail forward (when it is lagging) have
their linearization points at the update to tail. We consider these as
additonal LP's. As before, we present the robustness preserving
transformation of the above code, with the memory events marked as comments
in the code -

```c
void enq(int v) {
  while(true) {
    node* n = malloc(sizeof(node));
    atomic_store_explicit(&(n->val), v, memory_order_relaxed);                // E1
    node* t = atomic_load_explicit(tail, memory_order_acquire);               // E2
    node* next = atomic_load_explicit(&(tail->next), memory_order_acquire);   // E3
    
    if(next == NULL) {
      bcas_explicit(&(t->next), next, n, memory_order_acqrel))                // E4
      atomic_compare_exchange_strong(tail, t, next, memory_order_acqrel);     // E5
      break;
    }
    else { 
      bcas_explicit(tail, t, next, memory_order_acqrel);                      // E6
    }
  }
}

int deq() {
  node* h = atomic_load_explicit(head, memory_order_acquire);                 // D1
  node* t = atomic_load_explicit(tail, memory_order_acquire);                 // D2
  node* n = atomic_load_explicit(&(head->next), memory_order_relaxed);        // D3

  if (n == NULL) {
    return NULL;
  }

  if (h == l) {
    atomic_compare_exchange_strong(tail, t, n, memory_order_acqrel);         // D4
  }

  int r = atomic_load_explicit(&(n->val), memory_order_relaxed);             // D5
  bcas_explicit(head, h, n, memory_order_acqrel))                            // D6
  return r;
}
```

Next we present the encoding of the events - 

```smt
(assert (forall ((i I)) (=> (= (itype i) Enq) (and (= (etype (E1e i)) W) (= (elabel (E1e i)) Rlx)  (= (loc (E1e i)) (newloc i)) (= (stype (E1e i)) E1t) (= (field (E1e i)) Val) (= (wval (E1e i)) (argval i))))))

(assert (forall ((i I)) (=> (= (itype i) Enq) (and (= (etype (E2e i)) R) (= (elabel (E2e i)) Acq) (= (loc (E2e i)) tail) (= (stype (E2e i)) E2t) (= (field (E2e i)) Default) (= (rval (E2e i)) (enqLast i))))))

(assert (forall ((i I)) (=> (= (itype i) Enq) (and (= (etype (E3e i)) R) (= (elabel (E3e i)) Rlx) (= (loc (E3e i)) (enqLast i)) (= (stype (E3e i)) E3t) (= (field (E3e i)) Next) (= (rval (E3e i)) (enqNext i))))))

(assert (forall ((i I)) (=> (and (= (itype i) Enq)  (= (enqNext i) NULL)) (and (= (loc (E4e i)) (enqLast i)) (= (elabel (E4e i)) Acqrel) (= (field (E4e i)) Next) (= (stype (E4e i)) E4t) (isBot (E6e i)) (= (rval (E4e i)) (enqNext i)) (= (etype (E4e i)) U) (= (wval (E4e i)) (newloc i))))))

(assert (forall ((i I)) (=> (and (= (itype i) Enq)  (= (enqNext i) NULL)) (and (isR (E5e i)) (= (elabel (E5e i) Acq)) (= (stype (E5e i)) E5t) (= (loc (E5e i)) tail) (= (field (E5e i)) Default)))))

(assert (forall ((i I)) (=> (and (= (itype i) Enq)  (= (enqNext i) NULL)  (= (rval (E5e i)) (enqLast i)) ) (and  (= (etype (E5e i)) U) (= (elabel (E5e i) AcqRel)) (= (wval (E5e i)) (newloc i))))))

(assert (forall ((i I)) (=> (and (= (itype i) Enq)  (= (enqNext i) NULL)  (not (= (rval (E5e i)) (enqLast i))))  (= (etype (E5e i)) R) (= (elabel (E5e i) Acq)))))

(assert (forall ((i I)) (=> (and (= (itype i) Enq)  (not (= (enqNext i) NULL)) ) (and (isBot (E4e i)) (isBot (E5e i))  (= (loc (E6e i)) tail) (= (field (E6e i)) Default) (= (stype (E6e i)) E6t) (= (rval (E6e i)) (enqLast i)) (= (etype (E6e i)) U) (= (elabel (E6e i) AcqRel)) ((= (wval (E6e i)) (enqNext i)))))))

(assert (forall ((i I)) (=> (= (itype i) Deq) (and (= (rval (D1e i)) (deqFirst i)) (= (elabel (D1e i) Acq)) (= (stype (D1e i)) D1t) (= (loc (D1e i)) head) (= (field (D1e i)) Default) (= (etype (D1e i)) R)))))

(assert (forall ((i I)) (=> (= (itype i) Deq) (and (= (rval (D2e i)) (deqLast i)) (= (elabel (D2e i) Acq)) (= (stype (D2e i)) D2t) (= (loc (D2e i)) tail) (= (field (D2e i)) Default) (= (etype (D2e i)) R)))))

(assert (forall ((i I)) (=> (= (itype i) Deq) (and (= (rval (D3e i)) (deqNext i)) (= (elabel (D3e i) Rlx)) (= (stype (D3e i)) D3t) (= (loc (D3e i)) (deqFirst i)) (= (field (D3e i)) Next) (= (etype (D3e i)) R)))))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (= (deqNext i) NULL) ) (and  (= (retval i) EMPTY) (isBot (D4e i)) (isBot (D5e i)) (isBot (D6e i))))))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (= (deqFirst i) (deqLast i)) (not (= (deqNext i) NULL))) (and (isR (D4e i)) (= (stype (D4e i)) D4t) (= (loc (D5e i)) tail) (= (field (D5e i)) Default)))))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (not (= (deqNext i) NULL))  (= (deqFirst i) (deqLast i)) (= (rval (D4e i)) (deqLast i))) (and (= (etype (D4e i)) U) (= (elabel (D4e i) AcqRel)) (= (wval (D4e i)) (deqNext i))))))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (not (= (deqNext i) NULL)) (= (deqFirst i) (deqLast i)) (not (= (rval (D4e i)) (deqLast i)))) (= (etype (D4e i)) R) (= (elabel (D4e i) Acq)))))

(assert (forall ((i I)) (=> (and (= (itype i) Deq)  (not (= (deqNext i) NULL))) (and (= (etype (D5e i)) R) (= (elabel (D5e i) Rlx)) (= (loc (D5e i)) (deqNext i)) (= (field (D5e i)) Val) (= (stype (D5e i)) D5t) (= (rval (D5e i)) (deqRetval i))))))

(assert (forall ((i I)) (=> (and (= (itype i) Deq)  (not (= (deqNext i) NULL))) (and (= (loc (D6e i)) head) (= (field (D6e i)) Default) (= (stype (D6e i)) D6t) (= (rval (D6e i)) (deqFirst i) ) (= (wval (D6e i)) (deqNext i)) (= (etype (D6e i)) U) (= elabel (D6e i) AcqRel) (= (retval i) (deqRetval i))))))
```

Followed by the encoding of the linearizability axioms -

```smt2
;Linearization Point Constraints
(declare-fun lp (I) E)
(assert (forall ((i I)) (=> (= (itype i) Enq) (and (= (etype (lp i)) U) (= (loc (lp i)) tail) (= (field (lp i)) Default) (= (wval (lp i)) (newloc i)) (= (rval (lp i)) (loc (E4e i)))))))
(assert (forall ((i I)) (=> (and (= (itype i) Enq) (= (enqNext i) NULL))  (hb (E4e i) (lp i)) )  ))

;LPs of matching enqueue and dequeue are in hb Order
(assert (forall ((ie I) (id I)) (=> (matchm ie id) (and (= (enqNext ie) NULL) (not (= (deqNext id) NULL)) (hb (E4e ie) (D6e id)) )) ))

;Empty axiom
(assert (forall ((id1 I) (ie I)) (exists ((id2 I))(=> (and (= (itype id1) Deq)  (= (retval id1) EMPTY) (= (itype ie) Enq) (= (enqNext ie) NULL) (hb (E4e ie) (D1e id1)) ) (and (= (itype id2) Deq) (matchm ie id2) (not (= (deqNext id2) NULL))  (hb (D6e id2) (D1e id1))  ) ))))
```

For this case, we have the following set of locations that we need to verify -

| Case | L    | L'   |
|------|------|------|
|   1  | Head | Head |
|   2  | Head | Tail |
|   3  | Head | Next |
|   4  | Head | Val  |
|   5  | Tail | Head | 
|   6  | Tail | Tail |
|   7  | Tail | Next |
|   8  | Tail | Val  |
|   9  | Next | Head |
|   10 | Next | Tail |
|   11 | Next | Next |
|   12 | Next | Val  |
|   13 | Val  | Head |
|   14 | Val  | Tail |
|   15 | Val  | Next |
|   16 | Val  | Val  |

We show the query for one such case -

```smt2
; Enq -> Enq , L = N.Next, L' = Tail
(assert (= (itype in1) Enq ))
(assert (= (enqNext in1) NULL))
(assert (= (itype in2) Enq ))
(assert (= (itype in3) Enq ))
(assert (= (enqNext in3) NULL))
(assert (fr (E2e in2) (E5e in3)))
(assert (not (hb (E4e in1) (E5e in3))))
```

## Detailed explanation of Non-blocking set
We verify the non-blocking set implementation from the book - Art of
Multiprocessor programming by Herlihy and Shavit. The set is implemented as a
linked-list where the values are stored in sorted order. Nodes are added by
performing a compare-and-swap on the next field of the node storing the value
smaller than the value being added. Node removal occurs by marking the node
to be removed. After this, threads cooperatively remove such marked threads.

In this example, note that we use a bit from the pointer to denote whether
a pointer is marked or not. In terms of the source code, this shows up
as the function `atomic_compare_exchange_strong_mark_explicit` which takes
an expected mark value and the mark to update. In the SMT encoding, this
can just be encoded as another field in the node pointer, as we can atomically
update both fields.

The code we consider is below -

```c
void add(int v) {
  node* pred, curr, succ;
  while(true) {
    retry: while(true) {
      pred = atomic_load_explicit(head, memory_order_relaxed);
      curr = atomic_load_explicit(&(pred->next), memory_order_relaxed);
      
      while(true) {
        succ = atomic_load_explicit(&(curr->next), memory_order_relaxed);
        
        while(is_marked(succ)) {
          if(!atomic_cas_mark_explicit(&(pred->next), curr, succ, 0, 0)); // LP, remove
            goto retry;
          curr = succ;
          succ = atomic_load_explicit(&(curr->next), memory_order_relaxed);
        }

        if(atomic_load_explicit(&(curr->val), memory_order_relaxed) >= v)
          break;

        pred = curr;
        curr = succ;
      }
    }

    node* n = malloc(sizeof(node));
    atomic_store_explicit(&(n->next), curr, memory_order_relaxed);
    if(atomic_cas_mark_explicit(&(pred->next), curr, node, 0, 0); // LP, add
      break;
  }
}

int remove(int v) {
  node* pred, curr, succ;
  while(true) {
    retry: while(true) {
      pred = atomic_load_explicit(head, memory_order_relaxed);
      curr = atomic_load_explicit(&(pred->next), memory_order_relaxed);
      
      while(true) {
        succ = atomic_load_explicit(&(curr->next), memory_order_relaxed);
        
        while(is_marked(succ)) {
          if(!atomic_cas_mark_explicit(&(pred->next), curr, succ, 0, 0)); // LP, remove
            goto retry;
          curr = succ;
          succ = atomic_load_explicit(&(curr->next), memory_order_relaxed);
        }

        if(atomic_load_explicit(&(curr->val), memory_order_relaxed) >= v)
          break;

        pred = curr;
        curr = succ;
      }
    }

    if(atomic_load_explicit(&(curr->val), memory_order_relaxed) != v)
      return 0;
    else {
      succ = atomic_load_explicit(&(curr->next), memory_order_relaxed);
      if(!atomic_cas_mark(&(curr->next), succ, succ, 0, 1))
        continue
      atomic_cas_mark(&(pred->next), curr, succ, 0, 0);
      return 1;
    }
  }
}
```

The comments of the form `LP, add` and `LP, remove` represent the linearization
points. As before, we present the robustness preserving transformation of the
above code, with the memory events marked as comments in the code -

```c
void add(int v) {
  node* pred, curr, succ;
  pred = atomic_load_explicit(head, memory_order_relaxed);                       // E1e
  curr = atomic_load_explicit(&(pred->next), memory_order_relaxed);              // E2e
  curr = succ;
  succ = atomic_load_explicit(&(curr->next), memory_order_relaxed);              // E3e
    
  atomic_compare_exchange_strong_mark_explicit(&(pred->next), curr, succ, 0, 0); // E4e
  succ = atomic_load_explicit(&(curr->next), memory_order_relaxed);              // E5e

  node* n = malloc(sizeof(node));
  atomic_store_explicit(&(n->next), curr, memory_order_relaxed);                 // E6e
  atomic_cas_mark_explicit(&(pred->next), curr, node, 0, 0);                     // E7e
}

int remove(int v) {
  node* pred, curr, succ;
  pred = atomic_load_explicit(head, memory_order_relaxed);                       // D1e
  curr = atomic_load_explicit(&(pred->next), memory_order_relaxed);              // D2e
  succ = atomic_load_explicit(&(curr->next), memory_order_relaxed);              // D3e
    
  atomic_compare_exchange_mark_explicit(&(pred->next), curr, succ, 0, 0));       // D4e      
  curr = succ;
  succ = atomic_load_explicit(&(curr->next), memory_order_relaxed);              // D5e

  succ = atomic_load_explicit(&(curr->next), memory_order_relaxed);              // D6e
  atomic_cas_mark(&(curr->next), succ, succ, 0, 1);                              // D7e
  atomic_cas_mark(&(pred->next), curr, succ, 0, 0);                              // D8e
}
```

Next we present the encoding of the events - 

```smt
(assert (forall ((i I)) (=> (= (itype i) Add) (and (= (etype (E1e i)) R) (= (elabel (E1e i)) Rlx)  (= (loc (E1e i)) (newloc i)) (= (stype (E1e i)) E1t) (= (field (E1e i)) Default) (= (wval (E1e i)) (argval i))))))

(assert (forall ((i I)) (=> (= (itype i) Add) (and (= (etype (E2e i)) R) (= (elabel (E2e i)) Rlx) (= (loc (E2e i)) (newloc i)) (= (stype (E2e i)) E2t) (= (field (E2e i)) Default) (= (rval (E2e i)))))))

(assert (forall ((i I)) (=> (= (itype i) Add) (and (= (etype (E3e i)) R) (= (elabel (E3e i)) Rlx) (= (loc (E3e i)) (newloc i)) (= (stype (E3e i)) E3t) (= (field (E3e i)) Default) (= (rval (E3e i)))))))

(assert (forall ((i I)) (=> (and (= (itype i) Add) (and (= (loc (E4e i)) (loc (E3e i))) (= etype (E4e i) U) (= (elabel (E4e i)) Acqrel) (= ismark (loc (E3e i))) (= (field (E4e i)) Next) (= (stype (E4e i)) E4t))))))

(assert (forall ((i I)) (=> (and (= (itype i) Add) (= (addNext i) NULL)) (and (isR (E5e i)) (= (elabel (E5e i) Acq)) (= (stype (E5e i)) E5t) (= (loc (E5e i)) tail) (= (field (E5e i)) Default)))))

(assert (forall ((i I)) (=> (and (= (itype i) Add) (= (addNext i) NULL) (= (rval (E5e i)) (enqLast i)) ) (and  (= (etype (E5e i)) U) (= (elabel (E5e i) AcqRel)) (= (wval (E5e i)) (newloc i))))))

(assert (forall ((i I)) (=> (and (= (itype i) Add)  (= (addNext i) NULL)  (not (= (rval (E5e i)) (enqLast i))))  (= (etype (E5e i)) R) (= (elabel (E5e i) Acq)))))

(assert (forall ((i I)) (=> (and (= (itype i) Add)  (not (= (addNext i) NULL)) ) (and (isBot (E4e i)) (isBot (E5e i))  (= (loc (E6e i)) tail) (= (field (E6e i)) Default) (= (stype (E6e i)) E6t) (= (rval (E6e i)) (enqLast i)) (= (etype (E6e i)) U) (= (elabel (E6e i) AcqRel)) ((= (wval (E6e i)) (addNext i)))))))

(assert (forall ((i I)) (=> (= (itype i) Rem) (and (= (rval (D1e i)) (remFirst i)) (= (elabel (D1e i) Acq)) (= (stype (D1e i)) D1t) (= (loc (D1e i)) head) (= (field (D1e i)) Default) (= (etype (D1e i)) R)))))

(assert (forall ((i I)) (=> (= (itype i) Rem) (and (= (rval (D2e i)) (remLast i)) (= (elabel (D2e i) Acq)) (= (stype (D2e i)) D2t) (= (loc (D2e i)) tail) (= (field (D2e i)) Default) (= (etype (D2e i)) R)))))

(assert (forall ((i I)) (=> (= (itype i) Rem) (and (= (rval (D3e i)) (remNext i)) (= (elabel (D3e i) Rlx)) (= (stype (D3e i)) D3t) (= (loc (D3e i)) (remFirst i)) (= (field (D3e i)) Next) (= (etype (D3e i)) R)))))

(assert (forall ((i I)) (=> (and (= (itype i) Rem) (= (remNext i) NULL) ) (and  (= (retval i) EMPTY) (isBot (D4e i)) (isBot (D5e i)) (isBot (D6e i))))))

(assert (forall ((i I)) (=> (and (= (itype i) Rem) (= (remFirst i) (remLast i)) (not (= (remNext i) NULL))) (and (isR (D4e i)) (= (stype (D4e i)) D4t) (= (loc (D5e i)) tail) (= (field (D5e i)) Default)))))

(assert (forall ((i I)) (=> (and (= (itype i) Rem) (not (= (remNext i) NULL))  (= (remFirst i) (remLast i)) (= (rval (D4e i)) (remLast i))) (and (= (etype (D4e i)) U) (= (elabel (D4e i) AcqRel)) (= (wval (D4e i)) (remNext i))))))

(assert (forall ((i I)) (=> (and (= (itype i) Rem) (not (= (remNext i) NULL)) (= (remFirst i) (remLast i)) (not (= (rval (D4e i)) (remLast i)))) (= (etype (D4e i)) R) (= (elabel (D4e i) Acq)))))

(assert (forall ((i I)) (=> (and (= (itype i) Rem)  (not (= (remNext i) NULL))) (and (= (etype (D5e i)) R) (= (elabel (D5e i) Rlx)) (= (loc (D5e i)) (remNext i)) (= (field (D5e i)) Val) (= (stype (D5e i)) D5t) (= (rval (D5e i)) (remRetval i))))))

(assert (forall ((i I)) (=> (and (= (itype i) Rem)  (not (= (remNext i) NULL))) (and (= (loc (D6e i)) head) (= (field (D6e i)) Default) (= (stype (D6e i)) D6t) (= (rval (D6e i)) (remFirst i) ) (= (wval (D6e i)) (remNext i)) (= (etype (D6e i)) U) (= elabel (D6e i) AcqRel) (= (retval i) (remRetval i))))))
```

Followed by the encoding of the linearizability axioms -

```smt2
;Linearization Point Constraints
(declare-fun lp (I) E)
(assert (forall ((i I)) (=> (= (itype i) Add) (and (= (etype (lp i)) U) (= (field (lp i)) Next) (= (wval (lp i)) (newloc i)) (= (rval (lp i)) (loc (E4e i)))))))
(assert (forall ((i I)) (=> (= (itype i) Rem) (and (= (etype (lp i)) U) (= (field (lp i)) Mark) (= (wval (lp i)) 

;LPs of matching add and remove are in hb Order
(assert (forall ((ie I) (id I)) (=> (matchm ie id) (and (= (addNext ie) NULL) (not (= (remNext id) NULL)) (hb (E4e ie) (D6e id)) )) ))

;Empty axiom
(assert (forall ((id1 I) (ie I)) (exists ((id2 I))(=> (and (= (itype id1) Rem)  (= (retval id1) EMPTY) (= (itype ie) Add) (= (addNext ie) NULL) (hb (E4e ie) (D1e id1)) ) (and (= (itype id2) Rem) (matchm ie id2) (not (= (remNext id2) NULL))  (hb (D6e id2) (D1e id1))  ) ))))
```

For this case, we have the following set of locations that we need to verify -

| Case | L     | L'    |
|------|-------|-------|
|   1  | Head  | Head  |
|   2  | Head  | Val   |
|   3  | Head  | Next  |
|   5  | Val   | Head  | 
|   6  | Val   | Val   |
|   7  | Val   | Next  |
|   10 | Next  | Head  |
|   11 | Next  | Val   |
|   12 | Next  | Next  |

We show the query for one such case -

```smt2
; Add->Add, 
(assert (= (itype in1) Add))
(assert (= (itype in2) Add))
(assert (fr (E4e in1) (E2e in2)))
(assert (not (hb (E4e in1) (E2e in2))))
```
