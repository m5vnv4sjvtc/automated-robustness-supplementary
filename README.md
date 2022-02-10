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
(declare-fun matchm (I I) Bool) ; utility function for use in axioms
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
    node* t = atomic_load_explicit(top, memory_order_acquire);
    if (t == NULL)
      return EMPTY; // LP, pop
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
(assert (forall ((i I)) (=> (= (itype i) Enq) (and (= (etype (E1e i)) W) (= (elabel (E1e i)) Rlx)  (= (loc (E1e i)) (newloc i)) (= (stype (E1e i)) E1t) (= (field (E1e i)) Val) (= (wval (E1e i)) (argval i)) (= (valevent i) (E1e i))  ) ) ))

(assert (forall ((i I)) (=> (= (itype i) Enq) (soE (E1e i) (E2e i)) ) ))
(assert (forall ((i I)) (=> (= (itype i) Enq) (and (= (etype (E2e i)) R) (= (elabel (E2e i)) Rlx)  (= (loc (E2e i)) head) (= (stype (E2e i)) E2t) (= (field (E2e i)) Default) (= (rval (E2e i)) (enqh i)) ) ) ))


(assert (forall ((i I)) (=> (= (itype i) Enq) (soE (E2e i) (E3e i)) ) ))
(assert (forall ((i I)) (=> (= (itype i) Enq) (and (= (etype (E3e i)) W) (= (elabel (E3e i)) Rlx)  (= (loc (E3e i)) (newloc i)) (= (stype (E3e i)) E3t) (= (field (E3e i)) Next) (= (wval (E3e i)) (enqh i)) ) ) ))


(assert (forall ((i I)) (=> (= (itype i) Enq) (soE (E3e i) (E4e i)) ) ))
(assert (forall ((i I)) (=> (= (itype i) Enq) (and (= (etype (E4e i)) U) (= (elabel (E4e i)) AcqRel)  (= (loc (E4e i)) head) (= (stype (E4e i)) E4t) (= (field (E4e i)) Default) (= (rval (E4e i)) (enqh i)) (= (wval (E4e i)) (newloc i) ) ) ) ))
```

Then we show the memory events corresponding to the pop method -

```smt
(assert (forall ((i I))
  (=> (= (itype i) Deq)
  (and
    (= (rval (D1e i)) (deqh i))
    (= (loc (D1e i)) top)
    (= (field (D1e i)) Default)
    (= (etype (D1e i)) R)
    (= (elabel (D1e i)) Acq)))))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (= (deqh i) NULL)) (and (= (retval i) EMPTY) (isBot (D2e i)) (isBot (D3e i)) (isBot (D4e i)) ) ) ))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (not (= (deqh i) NULL))) (and (= (rval (D2e i)) (deqv i)) (= (stype (D2e i)) D2t) (= (loc (D2e i)) (deqh i)) (= (field (D2e i)) Val) (= (etype (D2e i)) R) (= (elabel (D2e i)) Rlx) (soE (D1e i) (D2e i)) ) ) ))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (not (= (deqh i) NULL))) (and (= (rval (D3e i)) (deqn i)) (= (stype (D3e i)) D3t) (= (loc (D3e i)) (deqh i)) (= (field (D3e i)) Next) (= (etype (D3e i)) R) (= (elabel (D3e i)) Rlx) (soE (D2e i) (D3e i)) ) ) ))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (not (= (deqh i) NULL))) (and (= (retval i) (deqv i)) (= (rval (D4e i)) (deqh i)) (= (wval (D4e i)) (deqn i)) (= (stype (D4e i)) D4t) (= (loc (D4e i)) head) (= (field (D4e i)) Default) (= (etype (D4e i)) U) (= (elabel (D4e i)) AcqRel) (soE (D3e i) (D4e i)) ) ) ))

(assert (forall ((i I)) (=> (and (= (itype i) Deq) (not (= (deqh i) NULL))) (and (not (= (retval i) EMPTY)) (not (= (retval i) zero))) ) ) )
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

## Detailed explanation of Lock-free queue
We verify the following code for the Michael-Scott non-blocking queue - 

```c
void enqueue(int v) {
  while(true) {
    node* n = malloc(sizeof(node));
    atomic_store_explicit(&(n->val), v, memory_order_relaxed);
    node* t = atomic_load_explicit(tail, memory_order_acquire);
    node* next = atomic_load_explicit(&(tail->next), memory_order_acquire);
    
    if(next == NULL) {
      if(atomic_compare_exchange_strong(&(t->next), next, n, memory_order_acqrel))
        atomic_compare_exchange_strong(tail, t, next, memory_order_acqrel);
      }
      break;
    }

    else { 
      atomic_compare_exchange_strong(tail, t, next, memory_order_acqrel);
    }
  }
}

int dequeue() {
  while(true) {
    node* h = atomic_load_explicit(head, memory_order_acquire);
    node* t = atomic_load_explicit(tail, memory_order_acquire);
    node* n = atomic_load_explicit(&(head->next), memory_order_relaxed);

    if (n == NULL) {
      return NULL;
    }

    if (h == l) {
      atomic_compare_exchange_strong(tail, t, n, memory_order_acqrel);
      continue;
    }

    int r = atomic_load_explicit(&(n->val), memory_order_relaxed);
    if(atomic_compare_exchange_strong(head, h, n, memory_order_acqrel)) {
      break;
    }
  }

  return r;
}
```


## Detailed explanation of Non-blocking set
We verify the non-blocking set implementation from the book - Art of
Multiprocessor programming by Herlihy and Shavit. The set is implemented as a
linked-list where the values are stored in sorted order. Nodes are added by
performing a compare-and-swap on the next field of the node storing the value
smaller than the value being added. Node removal occurs by marking the node
to be removed. After this, threads cooperatively remove such marked threads.

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
          if(!atomic_cas_mark_explicit(&(pred->next), curr, succ, 0, 0));
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
    if(atomic_cas_mark_explicit(&(pred->next), curr, node, 0, 0);
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
          if(!atomic_cas_mark_explicit(&(pred->next), curr, succ, 0, 0));
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

