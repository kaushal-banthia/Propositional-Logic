#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX 10000

/**********************************************************/
/************** Stack Datatype and Operations *************/
/**********************************************************/

// stack structure declaration
typedef struct stackADT {
    char opr[MAX];
    int top;
} Stack;

// initialize stack
void initStack (Stack *stack)
{
    stack->top = -1;
}

// check whether stack is empty
int isEmptyStack (Stack *stack)
{
    return (stack->top == -1);
}

// check whether stack is full
int isFullStack (Stack *stack)
{
    return (stack->top == MAX-1);
}

// push an element into stack
void push (Stack *stack, char x)
{
    if (isFullStack(stack))
        printf("Error: Stack is Full!\n");
    else
        stack->opr[++(stack->top)] = x;
}

// pop an element from stack
char pop (Stack *stack)
{
    char x;
    if (isEmptyStack(stack))
        printf("Error: Stack is Empty!\n");
    else
        x = stack->opr[(stack->top)--];
    return x;
}

/**********************************************************/


/**********************************************************/
/*********** Binary Tree Datatype and Operations **********/
/**********************************************************/

// binary tree structure declaration
typedef struct binTree {
    char element;
    struct binTree *leftChild;
    struct binTree *rightChild;
} BT;

// creating a node in binary tree
BT *createNode (char el)
{
    BT *newNode;
    if ( (newNode=(BT *)malloc(sizeof(BT))) == NULL )
        printf("Error: Malloc Error in Creating Node!\n");
    else {
        newNode->element = el;
        newNode->leftChild = NULL;
        newNode->rightChild = NULL;
    }
    return (newNode);
}

// creating an exact replica of the the binary tree
BT *duplicate(BT *orig)
{
    BT *dup = NULL;
    if(orig != NULL) {
        dup = createNode(orig->element);
        dup->leftChild = duplicate(orig->leftChild);
        dup->rightChild = duplicate(orig->rightChild);
    }
    return (dup);
}

/**********************************************************/


/**********************************************************/
/******************** Utility Functions *******************/
/**********************************************************/

// structure holding propositional values
typedef struct PropVal {
    char prop;
    int val; // '0' for False and '1' for True
} PV;

// scan every propositional values (one by one) from user as input
PV *scanPropValueInput(int *n)
{
    unsigned int noProp, i;
    PV *pvarr;

    printf("Enter Total Number of Propositions: ");
    scanf("%u",&noProp);
    *n = noProp;

    pvarr = (PV *)malloc(noProp * sizeof(PV));

    for (i = 0; i < noProp; i++) {
        printf("Enter Proposition [%u] (Format: Name <SPACE> Value): ", i+1);
        scanf(" %c %d", &pvarr[i].prop, &pvarr[i].val);
    }
    return pvarr;
}

// determines whether p is a proposition including 0 or 1
int isProposition (char p)
{
    return ( ((p >= 'a') && (p <= 'z')) || ((p >= 'A') && (p <= 'Z')) || (p == '0') || (p == '1') );
}

// printing the validity and satisfiability flags
void printResult (int valid, int sat)
{
    printf("\nThe Given Formula is: < ");
    valid ? printf("VALID") : printf("INVALID");
    printf(" + ");
    sat ? printf("SATISFIABLE") : printf("UNSATISFIABLE");
    printf(" >\n\n");
}

//display postfix form of propositional formula (from internally represented string)
void displayPfForm(char *pfForm)
{
    int i;

    printf("Postfix Representation of Formula:");
    for(i = 0; pfForm[i] != '\0'; i++){
        if ( pfForm[i] == '-' )
            printf(" ->");
        else if (pfForm[i] == '~')
            printf(" <->");
        else
            printf(" %c", pfForm[i]);
    }
    printf("\n");
}

// count number of characters in the formula representing only propositions and operators
int noOfIdsInFormula (char *formula)
{
    int i, len = strlen(formula), count = 0;
    for(i = 0; i < len; i++){
        if ( (formula[i] != '(') && (formula[i] != ')') && (formula[i] != ' ') && (formula[i] != '\t') )
            count++;
    }
    return count;
}

// pre-defined priority of in-stack element
int inStackPriority (char operator){
    switch(operator){
        case '!': return 3; break;

        case '&':
        case '|': return 2; break;

        case '~':
        case '-': return 1; break;

        case '(': return 0; break;

        default : return -1; break;
    }
}

// pre-defined priority of in-coming element
int inComingPriority (char operator){
    switch(operator){
        case '!': return 4; break;

        case '&':
        case '|': return 2; break;

        case '~':
        case '-': return 1; break;

        case '(': return 4; break;

        default : return -1; break;
    }
}

// generate postfix formula from the given input formula
char *genPostFixFormula(char *formula)
{
    int noOfIds = noOfIdsInFormula(formula), i, len = strlen(formula), k;
    char *pf = (char *)malloc((noOfIds+1) * sizeof(char));
    char out;
    Stack *stack = (Stack *)malloc(sizeof(Stack));
    initStack(stack); push(stack,'#');

    for (i = 0, k = 0; i < len; i++){
        if ( (formula[i] != ' ') && (formula[i] != '\t') ){
            if ( isProposition(formula[i]) )
                pf[k++] = formula[i];
            else if (formula[i] == ')') {
                while ( (out = pop(stack)) != '(')
                    pf[k++] = out;
            }
            else {
                while ( inStackPriority(out = pop(stack)) >= inComingPriority(formula[i]) )
                    pf[k++] = out;
                push(stack, out);
                push(stack, formula[i]);
            }
        }
    }
    while( (out = pop(stack)) != '#' )
        pf[k++] = out;
    pf[k] = '\0';

    return pf;
}

// expression tree formation from postfix formula string
BT *ETF (char *pfForm, int start, int end)
{
    BT *et = NULL;

    // WRITE YOUR CODE HERE ...
    if (start == end)
        et = createNode(pfForm[start]);
    else if ((end-start) > 0 && pfForm[end] == '!')
    {
        et = createNode('!');
        et->rightChild = ETF(pfForm, start, end-1);
    }
    else if ((end-start) > 1)
    {
        et = createNode(pfForm[end]);

        int k = end-1;
        int ops_props = 0;
        while(1)
        {
            if (pfForm[k] == '&' || pfForm[k] == '-' || pfForm[k] == '!' || pfForm[k] == '~')
                ops_props++;
            else
                ops_props--;

            if (ops_props < 0)
                break;
            k--;
        }
        if (k == 0)
        {
            et->leftChild=ETF(pfForm, start, k);
            et->rightChild=ETF(pfForm, k+1, end-1);
        }
        else
        {
            et->leftChild=ETF(pfForm, start, k-1);
            et->rightChild=ETF(pfForm, k, end-1);
        }
    }
    return et;
}

// printing the expresion tree using inorder traversal
void ETP (BT *et)
{
    // WRITE YOUR CODE HERE ...
    if (et != NULL)
    {
        if (et->leftChild == NULL && et->rightChild == NULL)
        {
            printf(" %c", et->element);
            return;
        }

        if (et->element == '!')
        {
            printf(" %c", et->element);
            ETP(et->rightChild);
        }
        else
        {
            printf(" (");
            ETP(et->leftChild);
            if (et->element == '-')
                printf(" ->");
            else
                printf(" %c", et->element);
            ETP(et->rightChild);
            printf(" )");
        }
    }
    return;
}

// evaluate the formula from the expression tree from the proposition values provided in varr[] array
int EVAL (BT *et, PV *pvarr, int size)
{
    int result;
    // WRITE YOUR CODE HERE ...
    if (isProposition(et->element))
    {
        for (int i = 0; i < size; i++)
        {
            if (et->element == pvarr[i].prop)
            {
                result = pvarr[i].val;
                break;
            }
        }
    }

    else if (et->element == '!')
    {
        result = !EVAL(et->rightChild, pvarr, size);
    }

    else if (et->element == '&')
    {
        result = (EVAL(et->leftChild, pvarr, size))&&(EVAL(et->rightChild, pvarr, size));
    }

    else if (et->element == '|')
    {
        result = EVAL(et->leftChild, pvarr, size)||EVAL(et->rightChild, pvarr, size);
    }

    else if (et->element == '-')
    {
        result = !EVAL(et->leftChild, pvarr, size)||EVAL(et->rightChild, pvarr, size);
    }

    else if (et->element == '~')
    {
        result = (!EVAL(et->leftChild, pvarr, size)||EVAL(et->rightChild, pvarr, size)) && (!EVAL(et->rightChild, pvarr, size)||EVAL(et->leftChild, pvarr, size));
    }
    return result;
}

// convert expression tree to IFF expression tree
BT *IFF (BT *et)
{
    // WRITE YOUR CODE HERE ...
    if (et->element == '-')
    {
        et->element = '|';
        BT *temp = et->leftChild;
        BT *newnode = createNode('!');
        newnode->rightChild = temp;
        et->leftChild = newnode;
    }
    else if (et->element == '~')
    {
        BT *a = et->leftChild;
        BT *b = et->rightChild;
        et->element = '&';
        BT *leftnewnode = createNode('|');
        BT *rightnewnode = createNode('|');
        BT *leftleftnewnode = createNode('!');
        BT *rightleftnewnode = createNode('!');

        et->leftChild = leftnewnode;
        et->rightChild = rightnewnode;
        leftnewnode->leftChild = leftleftnewnode;
        rightnewnode->leftChild = rightleftnewnode;
        leftnewnode->rightChild = b;
        rightnewnode->rightChild = a;
        leftleftnewnode->rightChild = duplicate(a);
        rightleftnewnode->rightChild = duplicate(b);
    }

    if (et->leftChild != NULL)
        et->leftChild = IFF(et->leftChild);
    if (et->rightChild !=NULL)
        et->rightChild = IFF(et->rightChild);

    return et;
}

// convert IFF expression tree to NNF expression tree
BT *NNF (BT *etI)
{
    // WRITE YOUR CODE HERE ...

    if (etI->element == '!')
    {
        if (etI->rightChild->element == '!')
            etI = etI->rightChild->rightChild;
        else if (etI->rightChild->element == '&')
        {
            BT *left = createNode('!');
            BT *right = createNode('!');
            left->rightChild = etI->rightChild->leftChild;
            right->rightChild = etI->rightChild->rightChild;
            etI->element = '|';
            etI->leftChild = left;
            etI->rightChild = right;
        }

        else if (etI->rightChild->element == '|')
        {
            BT *left = createNode('!');
            BT *right = createNode('!');
            left->rightChild = etI->rightChild->leftChild;
            right->rightChild = etI->rightChild->rightChild;
            etI->element = '&';
            etI->leftChild = left;
            etI->rightChild = right;
        }
    }

    if (etI->leftChild != NULL)
        etI->leftChild = NNF(etI->leftChild);
    if (etI->rightChild !=NULL)
        etI->rightChild = NNF(etI->rightChild);
    return etI;
}

// convert NNF expression tree to CNF expression tree
BT *CNF (BT *etN)
{
    // WRITE YOUR CODE HERE ...
    if (etN->element == '|')
    {
        if (etN->leftChild->element == '&')
        {
            etN->element = '&';
            BT *a = etN->leftChild->leftChild;
            BT *b = etN->leftChild->rightChild;
            BT *c = etN->rightChild;

            BT *left = createNode('|');
            BT *right = createNode('|');

            etN->leftChild = left;
            etN->rightChild = right;

            left->leftChild = a;
            left->rightChild = c;
            right->leftChild = b;
            right->rightChild = duplicate(c);
        }
        if (etN->rightChild->element == '&')
        {
            etN->element = '&';
            BT *a = etN->leftChild;
            BT *b = etN->rightChild->leftChild;
            BT *c = etN->rightChild->rightChild;

            BT *left = createNode('|');
            BT *right = createNode('|');

            etN->leftChild = left;
            etN->rightChild = right;

            left->leftChild = CNF(a);
            left->rightChild = CNF(b);
            right->leftChild = CNF(duplicate(a));
            right->rightChild = CNF(c);
        }
    }

    if (etN->leftChild != NULL)
        etN->leftChild = CNF(etN->leftChild);
    if (etN->rightChild !=NULL)
        etN->rightChild = CNF(etN->rightChild);

    return etN;
}

// convert NNF expression tree to DNF expression tree
BT *DNF (BT *etN)
{
    // WRITE YOUR CODE HERE ...
    if (etN->element == '&')
    {
        if (etN->leftChild->element == '|')
        {
            etN->element = '|';
            BT *a = etN->leftChild->leftChild;
            BT *b = etN->leftChild->rightChild;
            BT *c = etN->rightChild;

            BT *left = createNode('&');
            BT *right = createNode('&');

            etN->leftChild = left;
            etN->rightChild = right;

            left->leftChild = a;
            left->rightChild = c;
            right->leftChild = b;
            right->rightChild = duplicate(c);
        }
        if (etN->rightChild->element == '|')
        {
            etN->element = '|';
            BT *a = etN->leftChild;
            BT *b = etN->rightChild->leftChild;
            BT *c = etN->rightChild->rightChild;

            BT *left = createNode('&');
            BT *right = createNode('&');

            etN->leftChild = left;
            etN->rightChild = right;

            left->leftChild = DNF(a);
            left->rightChild = DNF(b);
            right->leftChild = DNF(duplicate(a));
            right->rightChild = DNF(c);
        }
    }

    if (etN->leftChild != NULL)
        etN->leftChild = DNF(etN->leftChild);
    if (etN->rightChild !=NULL)
        etN->rightChild = DNF(etN->rightChild);
    return etN;
}

int searcher(PV *p, int size, int start, BT *et, int *values, int i)
{
    if (start == size)
    {
        values[i] = EVAL(et, p, size);
        printf("    { ");
        for (int j = 0; j < size; j++)
        {
            printf("(%c = %d) ", p[j].prop, p[j].val);
        }
        printf("} : %d\n", values[i]);
        return i+1;
    }
    else
    {
        p[start].val = 0;
        i = searcher(p, size, start+1, et, values, i);
        p[start].val = 1;
        i = searcher(p, size, start+1, et, values, i);
        return i;
    }
}

// exhaustive search for checking validity / satisfiability
void CHECK (BT *et)
{
    int valid = 1, sat = 0;

    // WRITE YOUR CODE HERE ...
    printf("\nEnter Number of Propositions: ");
    int size;
    scanf("%d", &size);
    printf("Enter Proposition Names (<SPACE> Separated): ");
    PV p[size];
    for (int i = 0; i < size; i++)
    {
        char e;
        scanf(" %c", &e);
        p[i].prop = e;
    }

    int pow_size = (int)pow(2, size);
    int values[pow_size];
    printf("Evaluations of the Formula:\n");
    searcher(p, size, 0, et, &values[0], 0);
    int trues = 0;
    int falses = 0;
    for (int i = 0; i < pow_size; i++)
    {
        if (values[i] == 0)
            falses++;
        else
            trues++;
    }

    if (trues == pow_size)
    {
        valid = 1;
        sat = 1;
    }

    else if (falses == pow_size)
    {
        valid = 0;
        sat = 0;
    }

    else
    {
        valid = 0;
        sat = 1;
    }

    printResult(valid,sat);
}



// main routine
int main ()
{
    char formula[MAX], *pfForm;
    int len, i;

    BT *et, *etI, *etN, *etDup, *etC, *etD;
    int *varr;
    PV *pvarr;
    int result;

    // scan propositional formula from user input
    printf("\nEnter Propositional Logic Formula: ");
    scanf("%[^\n]", formula);

    // internal formula string with operators as, AND (&), OR (|), NOT (!), IMPLY (-) and IFF (~)
    len = strlen(formula);
    for(i = 0; i < len; i++){
        if(formula[i] == '<'){ // denoting iff operator (<->) using ~
            formula[i] = ' ';
            formula[i+1] = '~';
        }
        if(formula[i] == '>'){ // denoting imply operator (->) using -
            formula[i] = ' ';
        }
    }

    // postfix form generation from represented formula string
    pfForm = genPostFixFormula(formula);

    // display postfix form of the internally represented formula
    displayPfForm(pfForm);

    // internal postfix formula string with operators as, AND (&), OR (|), NOT (!), IMPLY (-) and IFF (~)
    printf("\n++++ PostFix Format of the Propositional Formula ++++\n('-' used for '->' and '~' used for '<->')\n");
    printf("YOUR INPUT STRING: %s\n", pfForm);

    printf("\n++++ Expression Tree Generation ++++");
    et = ETF(pfForm, 0, strlen(pfForm)-1);
    printf("\nOriginal Formula (from Expression Tree):");
    ETP(et);
    printf("\n");

    printf("\n++++ Expression Tree Evaluation ++++\n");
    int size;
    pvarr = scanPropValueInput(&size);
    result = EVAL(et, pvarr, size);
    printf("\nThe Formula is Evaluated as: ");
    (result) ? printf("True\n") : printf("False\n");

    printf("\n++++ IFF Expression Tree Conversion ++++");
    etI = IFF(et);
    printf("\nFormula in Implication Free Form (IFF from Expression Tree):");
    ETP(etI);
    printf("\n");

    printf("\n++++ NNF Expression Tree Conversion ++++");
    etN = NNF(etI);
    printf("\nFormula in Negation Normal Form (NNF from Expression Tree):");
    ETP(etN);
    printf("\n");

    etDup = duplicate(etN); // keeping a duplicate copy for DNF conversion

    printf("\n++++ CNF Expression Tree Conversion ++++");
    etC = CNF(etN);
    printf("\nFormula in Conjunctive Normal Form (CNF from Expression Tree):");
    ETP(etC);
    printf("\n");

    printf("\n++++ DNF Expression Tree Conversion ++++");
    etD = DNF(etDup);
    printf("\nFormula in Disjunctive Normal Form (DNF from Expression Tree):");
    ETP(etD);
    printf("\n");

    printf("\n++++ Exhaustive Search from Expression Tree for Validity / Satisfiability Checking ++++");
    CHECK (et);

    return 0;
}
