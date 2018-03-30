/*
The implementation of dFIN algorithm, “Zhi-Hong Deng. DiffNodesets: An efficient structure for fast mining frequent itemsets. Applied Soft Computing, 41: 214-223, 2016”.
 */

/* 
 * File:   dFIN.cpp
 * Author: Nader Aryabarzan
 * Email: aryabarzan@aut.ac.ir,aryabarzan@gmail.com
 *
 * Created on March 3, 2017
 */

#include <cstdlib>
#include<iostream>
#include <stdio.h>
#include <cmath>
#include<time.h>
#include <windows.h>
#include <psapi.h>
#include <cstring>
#include <fstream>


using namespace std;
int dump;


//==========================================
int **__buffer;
int __bf_cursor;
int __bf_size;
int __bf_col;
int __bf_currentSize;

int __numOfFItem;
int __Min_Support;

double __sume_of_key_operation_in_diff_algorithm=0;
double __sume_of_key_operation_in_neg_algorithm=0;
double __number_of_merges=0;
double __first_ns_Lenght=0;
double __second_ns_length=0;

struct __Item {
    int index;
    int num;
};

__Item *__item;

struct __NodeListTreeNode {
    int label;
    __NodeListTreeNode* firstChild;
    __NodeListTreeNode* next;
    int support;
    int NLStartinBf;
    int NLLength;
    int NLCol;
    //LinkItem *sameItemList;
};

struct __PPCTreeNode {
    int label;
    __PPCTreeNode* firstChild;
    __PPCTreeNode* rightSibling;
    __PPCTreeNode* father;
    int count;
    __int128 foreIndex;
    //YYY ???{
    __int128 postIndex;
    //YYY ???}
};

__PPCTreeNode *__ppcRoot;

__NodeListTreeNode __nlRoot;
int __nlNodeCount = 0;
int __resultCount = 0;
long long __nlLenSum = 0;


FILE *__out;
int *__result;
int __resultLen = 0;

void __showMemoryInfo(void) {
    HANDLE handle = GetCurrentProcess();
    PROCESS_MEMORY_COUNTERS pmc;
    //    GetProcessMemoryInfo(handle,&pmc,sizeof(pmc));
    cout << pmc.PeakWorkingSetSize / 1000 << endl;
}

int __comp(const void *a, const void *b) {
    return (*(__Item *) b).num - (*(__Item *) a).num;
}

void __getData(FILE * in, char *filename, double support) {
    if ((in = fopen(filename, "r")) == NULL) {
        cout << "read wrong!" << endl;
        fclose(in);
        exit(1);
    }

    char str[500];
    __Item **tempItem = new __Item*[10];
    tempItem[0] = new __Item[10000];
    for (int i = 0; i < 10000; i++) {
        tempItem[0][i].index = i;
        tempItem[0][i].num = 0;
    }

    int numOfTrans = 0;
    int size = 1;
    int numOfItem = 0;
    int num = 0;
    int col = 0;
    while (fgets(str, 500, in)) {
        //???XXX Commented
        //		if(feof(in)) break;
        numOfTrans++;
        num = 0;
        for (int i = 0; i < 500 && str[i] != '\0'; i++) {
            if (str[i] != ' ') num = num * 10 + str[i] - '0';
            else {
                col = num / 10000;
                if (col >= size) {
                    for (int j = size; j <= col; j++) {
                        tempItem[j] = new __Item[10000];
                        for (int p = 0; p < 10000; p++) {
                            tempItem[j][p].index = j * 10000 + p;
                            tempItem[j][p].num = 0;
                        }
                    }
                    size = col + 1;
                }
                if (0 == tempItem[col][num % 10000].num++) numOfItem++;
                num = 0;
            }
        }
        //XXX inserted
        if (feof(in)) break;
    }
    fclose(in);

    __Min_Support = int(support * numOfTrans);
    __item = new __Item[numOfItem];
    for (int i = 0, p = 0; i < size; i++)
        for (int j = 0; j < 10000; j++)
            if (tempItem[i][j].num != 0)
                __item[p++] = tempItem[i][j];

    for (int i = 0; i < size; i++)
        delete[] tempItem[i];
    delete[] tempItem;

    qsort(__item, numOfItem, sizeof (__Item), __comp);

    for (__numOfFItem = 0; __numOfFItem < numOfItem; __numOfFItem++)
        if (__item[__numOfFItem].num < __Min_Support)
            break;

}


//int *__itemsetCount;
int *__nlistBegin;
int __nlistCol;
int *__nlistLen;
int __firstNlistBegin;

int __PPCNodeCount;
int *__SupportDict;
int *__postOrderDict;
int *__sameItems;

void __buildTree(FILE *in, char * filename) {
    if ((in = fopen(filename, "r")) == NULL) {
        cout << "read wrong!" << endl;
        fclose(in);
        exit(1);
    }

    __PPCNodeCount = 0;
    //XXX ??? inserted

    __ppcRoot = new __PPCTreeNode;
    //XXX ??? commented
    //ppcRoot.label = -1;
    //XXX ??? BEGIN inserted
    __ppcRoot->label = -1;
    __ppcRoot->count = 0;
    __ppcRoot->father = NULL;
    __ppcRoot->firstChild = NULL;
    __ppcRoot->rightSibling = NULL;
    __ppcRoot->foreIndex = 0;
    __ppcRoot->postIndex = 0;
    //XXX ??? END inserted


    //YYY ??? inserted
    //        _itemsetCount = new int[ numOfFItem ];
    __nlistBegin = new int[ __numOfFItem ];
    __nlistLen = new int[ __numOfFItem ];
    //	memset(_itemsetCount, 0, sizeof(int) *  numOfFItem);
    memset(__nlistLen, 0, sizeof (int) * __numOfFItem);
    //End YYY ??? inserted

    char str[500];
    __Item transaction[1000];
    for (int i = 0; i < 1000; i++) {
        transaction[i].index = 0;
        transaction[i].num = 0;
    }

    int num = 0, tLen = 0;
    while (fgets(str, 500, in)) {

        num = 0;
        tLen = 0;
        for (int i = 0; i < 500 && str[i] != '\0'; i++) {
            if (str[i] != ' ') num = num * 10 + str[i] - '0';
            else {
                for (int j = 0; j < __numOfFItem; j++) {
                    if (num == __item[j].index) {
                        transaction[tLen].index = num;
                        transaction[tLen].num = 0 - j;
                        tLen++;
                        break;
                    }
                }
                num = 0;
            }
        }

        qsort(transaction, tLen, sizeof (__Item), __comp);
        int curPos = 0;
        //XXX ??? Commented
        //PPCTreeNode *curRoot =&(ppcRoot);
        //XXX ??? inserted
        __PPCTreeNode *curRoot = __ppcRoot;

        __PPCTreeNode *leftSibling = NULL;
        while (curPos != tLen) {
            __PPCTreeNode *child = curRoot->firstChild;
            while (child != NULL) {
                if (child -> label == 0 - transaction[curPos].num) {
                    curPos++;
                    child->count++;
                    curRoot = child;
                    break;
                }
                if (child -> rightSibling == NULL) {
                    leftSibling = child;
                    child = NULL;
                    break;
                }
                child = child -> rightSibling;
            }
            if (child == NULL) break;
        }
        for (int j = curPos; j < tLen; j++) {
            __PPCTreeNode *ppcNode = new __PPCTreeNode;
            ppcNode->label = 0 - transaction[j].num;

            ppcNode->rightSibling = NULL;
            ppcNode->firstChild = NULL;
            ppcNode->father = curRoot;
            ppcNode->count = 1;

            if (leftSibling != NULL) {
                if (ppcNode->label < curRoot->firstChild->label) {
                    ppcNode->rightSibling = curRoot->firstChild;
                    curRoot->firstChild = ppcNode;
                } else {
                    leftSibling = curRoot->firstChild;
                    do {
                        if (leftSibling->rightSibling == NULL) {
                            leftSibling->rightSibling = ppcNode;
                            leftSibling = NULL;
                            break;
                        } else if (ppcNode->label < leftSibling->rightSibling->label) {
                            ppcNode->rightSibling = leftSibling->rightSibling;
                            leftSibling->rightSibling = ppcNode;
                            leftSibling = NULL;
                            break;
                        } else {
                            leftSibling = leftSibling->rightSibling;
                        }
                    } while (1);

                }

                //                leftSibling->rightSibling = ppcNode;
                leftSibling = NULL;
            } else {
                curRoot->firstChild = ppcNode;
            }

            curRoot = ppcNode;
            __PPCNodeCount++;
            __nlistLen[ppcNode->label]++;
        }
        if (feof(in))
            break;
    }
    fclose(in);
    //        int curPos = 0;
    //        //XXX ??? Commented
    //        //PPCTreeNode *curRoot =&(ppcRoot);
    //        //XXX ??? inserted
    //        __PPCTreeNode *curRoot = __ppcRoot;
    //
    //        __PPCTreeNode *leftSibling = NULL;
    //        while (curPos < tLen) {
    //            __PPCTreeNode *child = curRoot->firstChild;
    //
    //            while (child != NULL) {
    //                if (child->label == 0 - transaction[curPos].num) {
    //                    curPos++;
    //                    child->count++;
    //                    curRoot = child;
    //                    break;
    //                }
    //                if (0 - transaction[curPos].num < child->label) {//stop!
    //                    __PPCTreeNode *ppcNode = new __PPCTreeNode;
    //                    ppcNode->label = 0 - transaction[curPos++].num;
    //                    ppcNode->firstChild = NULL;
    //                    ppcNode->father = curRoot;
    //                    ppcNode->count = 1;
    //                    //YYY ??? {
    //                    ppcNode->postIndex = 0;
    //                    //YYY ??? }
    //
    //                    __PPCNodeCount++;
    //                    __nlistLen[ppcNode->label]++;
    //
    //                    ppcNode->rightSibling = child;
    //                    if (leftSibling == NULL) { //first position                      
    //                        curRoot->firstChild = ppcNode;
    //                    } else {
    //                        leftSibling->rightSibling = ppcNode;
    //                    }
    //                    curRoot = ppcNode;
    //                    child = curRoot->father;
    //                    break;
    //
    //                } else {
    //                    leftSibling = child;
    //                    child = child -> rightSibling;
    //                }
    //
    //            }
    //            if (child == NULL) break;
    //        }
    //        for (int j = curPos; j < tLen; j++) {
    //            __PPCTreeNode *ppcNode = new __PPCTreeNode;
    //            ppcNode->label = 0 - transaction[j].num;
    //
    //            curRoot->firstChild = ppcNode;
    //
    //            ppcNode->rightSibling = NULL;
    //            ppcNode->firstChild = NULL;
    //            ppcNode->father = curRoot;
    //            ppcNode->count = 1;
    //            //YYY ??? {
    //            ppcNode->postIndex = 0;
    //            //YYY ??? }
    //            curRoot = ppcNode;
    //            __PPCNodeCount++;
    //            __nlistLen[ppcNode->label]++;
    //        }
    //        if (feof(in))
    //            break;
    //    }
    //    fclose(in);

    //YYY ??? inserted
    //build 1-itemset nlist
    int __sum = 0;
    for (int i = 0; i < __numOfFItem; i++) {
        __nlistBegin[i] = __sum;
        __sum += __nlistLen[i];
    }

    if (__bf_cursor + __sum > __bf_currentSize * 0.85) {
        __bf_col++;
        __bf_cursor = 0;
        __bf_currentSize = __sum + 1000;
        __buffer[__bf_col] = new int[__bf_currentSize];
    }
    __nlistCol = __bf_col;
    __firstNlistBegin = __bf_cursor;
    __bf_cursor += __sum;
    //End YYY ??? inserted


    //XXX ??? Commented
    //	PPCTreeNode *root = ppcRoot.firstChild;
    //XXX ??? inserted
    __PPCTreeNode *root = __ppcRoot->firstChild;
    int pre = 0;
    //YYY ???{
    int post = 0;
    //YYY ???}

    //YYY ??? Commented
    /*
    itemsetCount = new int[(numOfFItem-1) * numOfFItem / 2];
    nlistBegin = new int[(numOfFItem-1) * numOfFItem / 2];
    nlistLen = new int[(numOfFItem-1) * numOfFItem / 2];
    memset(itemsetCount, 0, sizeof(int) * (numOfFItem-1) * numOfFItem / 2);
    memset(nlistLen, 0, sizeof(int) * (numOfFItem-1) * numOfFItem / 2);
     */


    __SupportDict = new int[__PPCNodeCount + 1];
    //YYY ???{
    __postOrderDict = new int[__PPCNodeCount + 1];
    //YYY ???}
    while (root != NULL) {
        root->foreIndex = pre;
        __SupportDict[pre] = root->count;
        int cursor = __nlistBegin[root->label] + __firstNlistBegin;
        __buffer[__nlistCol][cursor] = pre;
        __nlistBegin[root->label]++;
        pre++;
        //        __PPCTreeNode *temp = root->father;
        //        while (temp->label != -1) {
        //            __itemsetCount[root->label * (root->label - 1) / 2 + temp->label] += root->count;
        //            __nlistLen[root->label * (root->label - 1) / 2 + temp->label]++;
        //            temp = temp->father;
        //        }
        if (root->firstChild != NULL)
            root = root->firstChild;
        else {
            if (root != __ppcRoot) {
                root->postIndex = post;
                __postOrderDict[root->foreIndex] = post;
                post++;
            }
            if (root->rightSibling != NULL)
                root = root->rightSibling;
            else {
                root = root->father;



                while (root != NULL) {
                    if (root != __ppcRoot) {
                        root->postIndex = post;
                        __postOrderDict[root->foreIndex] = post;
                        post++;
                    }

                    if (root->rightSibling != NULL) {
                        root = root->rightSibling;
                        break;
                    }
                    root = root->father;

                }

            }
        }
    }


    //YYY ??? inserted
    for (int i = 0; i < __numOfFItem; i++) {
        __nlistBegin[i] = __nlistBegin[i] - __nlistLen[i];

    }
    //END YYY ??? inserted

    //build 2-itemset nlist
    //    int sum = 0;
    //    for (int i = 0; i < (__numOfFItem - 1) * __numOfFItem / 2; i++)
    //        if (__itemsetCount[i] >= __Min_Support) {
    //            __nlistBegin[i] = sum;
    //            sum += __nlistLen[i];
    //        }
    //    if (__bf_cursor + sum > __bf_currentSize * 0.85) {
    //        __bf_col++;
    //        __bf_cursor = 0;
    //        __bf_currentSize = sum + 1000;
    //        __buffer[__bf_col] = new int[__bf_currentSize];
    //    }
    //    __nlistCol = __bf_col;
    //    __firstNlistBegin = __bf_cursor;
    //    //XXX ??? Commented
    //    //	root = ppcRoot.firstChild;
    //    //XXX ??? inserted
    //    root = __ppcRoot->firstChild;
    //
    //
    //    __bf_cursor += sum;
    //    while (root != NULL) {
    //
    //        __PPCTreeNode *temp = root->father;
    //        //            printf("tree node=>label=%d,count=%d \en",temp->label,temp->count);
    //        while (temp->label != -1) {
    //            if (__itemsetCount[root->label * (root->label - 1) / 2 + temp->label] >= __Min_Support) {
    //                int cursor = __nlistBegin[root->label * (root->label - 1) / 2 + temp->label] + __firstNlistBegin;
    //                __buffer[__nlistCol][cursor] = root->foreIndex;
    //                __nlistBegin[root->label * (root->label - 1) / 2 + temp->label] += 1;
    //            }
    //            temp = temp->father;
    //        }
    //        if (root->firstChild != NULL)
    //            root = root->firstChild;
    //        else {
    //            if (root->rightSibling != NULL)
    //                root = root->rightSibling;
    //            else {
    //                root = root->father;
    //                while (root != NULL) {
    //                    if (root->rightSibling != NULL) {
    //                        root = root->rightSibling;
    //                        break;
    //                    }
    //                    root = root->father;
    //                }
    //            }
    //        }
    //    }
    //    for (int i = 0; i < __numOfFItem * (__numOfFItem - 1) / 2; i++)
    //        if (__itemsetCount[i] >= __Min_Support) {
    //            __nlistBegin[i] = __nlistBegin[i] - __nlistLen[i];
    //        }
}

void __initializeTree() {
    __NodeListTreeNode *lastChild = NULL;

    for (int t = __numOfFItem - 1; t >= 0; t--) {
        __NodeListTreeNode *nlNode = new __NodeListTreeNode;
        nlNode->label = t;
        nlNode->support = 0;
        nlNode->NLStartinBf = __nlistBegin[t]; //YYY ??? __bf_cursor;
        nlNode->NLLength = __nlistLen[t];

        nlNode->NLCol = __bf_col;
        nlNode->firstChild = NULL;
        nlNode->next = NULL;
        nlNode->support = __item[t].num;
        if (__nlRoot.firstChild == NULL) {
            __nlRoot.firstChild = nlNode;
            lastChild = nlNode;
        } else {
            lastChild->next = nlNode;
            lastChild = nlNode;
        }
    }
}

__NodeListTreeNode *__isk_itemSetFreq(__NodeListTreeNode* ni, __NodeListTreeNode* nj, int level, __NodeListTreeNode *lastChild, int &sameCount) {
    if (__bf_cursor + ni->NLLength > __bf_currentSize) {
        __bf_col++;
        __bf_cursor = 0;
        __bf_currentSize = __bf_size > ni->NLLength * 1000 ? __bf_size : ni->NLLength * 1000;
        __buffer[__bf_col] = new int[__bf_currentSize];
    }

    __NodeListTreeNode *nlNode = new __NodeListTreeNode;
    nlNode->support = ni->support; //0;
    nlNode->NLStartinBf = __bf_cursor;
    nlNode->NLCol = __bf_col;
    nlNode->NLLength = 0;


    int cursor_i = ni->NLStartinBf;
    int cursor_j = nj->NLStartinBf;
    int col_i = ni->NLCol;
    int col_j = nj->NLCol;
    int node_indexI, node_indexJ;


    //     if (ni->label == 3 && nj->label == 2 && level == 2) {
    //        cout << "\nlabel " << ni->label << "\t";
    //        for (int ii = ni->NLStartinBf; ii < ni->NLStartinBf + ni->NLLength; ii++) {
    //            cout << "," << __buffer[ni->NLCol][ii];
    //        }
    //        cout << "\nlabel " << nj->label << "\t";
    //        for (int jj = nj->NLStartinBf; jj < nj->NLStartinBf + nj->NLLength; jj++) {
    //            cout << "," << __buffer[nj->NLCol][jj];
    //        }
    //        cout << "\n======\n ";
    //    }

    __number_of_merges++;
    __first_ns_Lenght+=ni->NLLength;
    __second_ns_length+=nj->NLLength;
    if(ni->NLLength!=0)__sume_of_key_operation_in_neg_algorithm+=nj->NLLength;


    
    while (cursor_i < ni->NLStartinBf + ni->NLLength && cursor_j < nj->NLStartinBf + nj->NLLength) {
        __sume_of_key_operation_in_diff_algorithm++;
        node_indexI = __buffer[col_i][cursor_i];
        //        postI = __postOrderDict[node_indexI];

        node_indexJ = __buffer[col_j][cursor_j];
        //        postJ = __postOrderDict[node_indexJ];
        if (node_indexJ < node_indexI) {
            cursor_j += 1;
            __buffer[__bf_col][__bf_cursor++] = node_indexJ;
            nlNode->support -= __SupportDict[node_indexJ];
            nlNode->NLLength++;
        } else if (node_indexJ > node_indexI)
            cursor_i += 1;
        else {
            cursor_i += 1;
            cursor_j += 1;
        }
    }

    while (cursor_j < nj->NLStartinBf + nj->NLLength) {
        node_indexJ = __buffer[col_j][cursor_j];
        __buffer[__bf_col][__bf_cursor++] = node_indexJ;
        nlNode->support -= __SupportDict[node_indexJ];
        nlNode->NLLength++;
        cursor_j++;
    }

    //    if (ni->label == 3 && nj->label == 2 && level == 2) {
    //        cout << "\nlabel " << ni->label << "\t";
    //        for (int ii = ni->NLStartinBf; ii < ni->NLStartinBf + ni->NLLength; ii++) {
    //            cout << "," << __buffer[ni->NLCol][ii];
    //        }
    //        cout << "\nlabel " << nj->label << "\t";
    //        for (int jj = nj->NLStartinBf; jj < nj->NLStartinBf + nj->NLLength; jj++) {
    //            cout << "," << __buffer[nj->NLCol][jj];
    //        }
    //
    //        cout << "\ndebug ";
    //        for (int kk = nlNode->NLStartinBf; kk < nlNode->NLStartinBf + nlNode->NLLength; kk++) {
    //            cout << "," << __buffer[nlNode->NLCol][kk];
    //        }
    //    }
    //    cout << "\n================\n";

    if (nlNode->support >= __Min_Support) {
        if (ni->support == nlNode->support)
            __sameItems[sameCount++] = nj->label;
        else {
            nlNode->label = nj->label;
            nlNode->firstChild = NULL;
            nlNode->next = NULL;
            if (ni->firstChild == NULL) {
                ni->firstChild = nlNode;
                lastChild = nlNode;
            } else {
                lastChild->next = nlNode;
                lastChild = nlNode;
            }
        }
        return lastChild;
    } else {
        __bf_cursor = nlNode->NLStartinBf;
        delete nlNode;
    }
    return lastChild;
}

__NodeListTreeNode* __is2_itemSetValid(__NodeListTreeNode* ni, __NodeListTreeNode* nj, int level, __NodeListTreeNode* lastChild, int &sameCount) {
    if (__bf_cursor + ni->NLLength > __bf_currentSize) {
        __bf_col++;
        __bf_cursor = 0;
        __bf_currentSize = __bf_size > ni->NLLength * 1000 ? __bf_size : ni->NLLength * 1000;
        __buffer[__bf_col] = new int[__bf_currentSize];
    }

    __NodeListTreeNode *nlNode = new __NodeListTreeNode;
    nlNode->support = ni->support;
    nlNode->NLStartinBf = __bf_cursor;
    nlNode->NLCol = __bf_col;
    nlNode->NLLength = 0;

    int cursor_i = ni->NLStartinBf;
    int cursor_j = nj->NLStartinBf;
    int col_i = ni->NLCol;
    int col_j = nj->NLCol;
    int preI, postI, preJ, postJ;

        __number_of_merges++;
        if(ni->NLLength!=0)__sume_of_key_operation_in_neg_algorithm+=nj->NLLength;
        __first_ns_Lenght+=ni->NLLength;
    __second_ns_length+=nj->NLLength;
    
    while (cursor_i < ni->NLStartinBf + ni->NLLength && cursor_j < nj->NLStartinBf + nj->NLLength) {
        __sume_of_key_operation_in_diff_algorithm++;
        
        
        preI = __buffer[col_i][cursor_i];
        postI = __postOrderDict[preI];

        preJ = __buffer[col_j][cursor_j];
        postJ = __postOrderDict[preJ];
        if (postI > postJ) {
            cursor_j++;
        } else if (postI < postJ && preI > preJ) {
            cursor_i++;
        } else {
            __buffer[__bf_col][__bf_cursor++] = preI;
            nlNode->support -= __SupportDict[preI];
            nlNode->NLLength++;
            cursor_i++;
        }

        //        if (__buffer[col_i][cursor_i] == __buffer[col_j][cursor_j]) {
        //            __buffer[__bf_col][__bf_cursor++] = preJ;//__buffer[col_j][cursor_j];
        //            nlNode->NLLength++;
        //            nlNode->support += __SupportDict[__buffer[col_i][cursor_i]];
        //            cursor_i += 1;
        //            cursor_j += 1;
        //        } else if (__buffer[col_i][cursor_i] < __buffer[col_j][cursor_j])
        //            cursor_i += 1;
        //        else
        //            cursor_j += 1;
    }
    while (cursor_i < ni->NLStartinBf + ni->NLLength) {
        preI = __buffer[col_i][cursor_i];
        __buffer[__bf_col][__bf_cursor++] = preI;
        nlNode->support -= __SupportDict[preI];
        nlNode->NLLength++;
        cursor_i++;
    }


    //    if(ni->label==3 && nj->label==2){
    //                        cout << "\n1label-> " << ni->label << "\t";
    //        for (int ii = ni->NLStartinBf; ii < ni->NLStartinBf + ni->NLLength; ii++) {
    //            cout << "," << __buffer[ni->NLCol][ii];
    //        }
    //        cout << "\n1label-> " << nj->label << "\t";
    //        for (int jj = nj->NLStartinBf; jj < nj->NLStartinBf + nj->NLLength; jj++) {
    //            cout << "," << __buffer[nj->NLCol][jj];
    //        }
    //
    //        cout << "\n1debug-> ";
    //        for (int kk = nlNode->NLStartinBf; kk < nlNode->NLStartinBf + nlNode->NLLength; kk++) {
    //            cout << "," << __buffer[nlNode->NLCol][kk];
    //        }
    //    }


    if (nlNode->support >= __Min_Support) {
        if (ni->support == nlNode->support)
            __sameItems[sameCount++] = nj->label;
        else {
            nlNode->label = nj->label;
            nlNode->firstChild = NULL;
            nlNode->next = NULL;
            if (ni->firstChild == NULL) {
                ni->firstChild = nlNode;
                lastChild = nlNode;
            } else {
                lastChild->next = nlNode;
                lastChild = nlNode;
            }
        }
        return lastChild;
    } else {
        __bf_cursor = nlNode->NLStartinBf;
        delete nlNode;
    }
    return lastChild;
}

void __traverse(__NodeListTreeNode *curNode, __NodeListTreeNode *curRoot, int level, int sameCount) {
   
    
    __NodeListTreeNode *sibling = curNode->next;
    __NodeListTreeNode *lastChild = NULL;

    while (sibling != NULL) {

    
        if (level == 1)
            lastChild = __is2_itemSetValid(curNode, sibling, level, lastChild, sameCount);
        else if (level > 1)
            lastChild = __isk_itemSetFreq(curNode, sibling, level, lastChild, sameCount);
        sibling = sibling->next;
    }


    __resultCount += pow(2.0, sameCount);
    __nlLenSum += ((double) curNode->NLLength * pow(2.0, sameCount));

    if (dump == 1) {
        __result[__resultLen++] = curNode->label;
        for (int i = 0; i < __resultLen; i++)
            fprintf(__out, "%d ", __item[__result[i]].index);
        fprintf(__out, "(%d %d)", curNode->support, curNode->NLLength);
        for (int i = 0; i < sameCount; i++)
            fprintf(__out, " %d", __item[__sameItems[i]].index);
        fprintf(__out, "\n");
    }
    __nlNodeCount++;

    int from_cursor = __bf_cursor;
    int from_col = __bf_col;
    int from_size = __bf_currentSize;
    __NodeListTreeNode *child = curNode->firstChild;
    __NodeListTreeNode *next = NULL;
    while (child != NULL) {
        next = child->next;
        __traverse(child, curNode, level + 1, sameCount);
        for (int c = __bf_col; c > from_col; c--)
            delete[] __buffer[c];
        __bf_col = from_col;
        __bf_cursor = from_cursor;
        __bf_currentSize = from_size;
        child = next;
    }
    if (dump == 1)
        __resultLen--;
    delete curNode;
}

void __deleteFPTree() {
    //XXX ??? Commented
    //        PPCTreeNode *root = ppcRoot.firstChild;
    //XXX ??? inserted
    __PPCTreeNode *root = __ppcRoot->firstChild;



    __PPCTreeNode *next = NULL;
    while (root != NULL) {
        if (root->firstChild != NULL)
            root = root->firstChild;
        else {
            if (root->rightSibling != NULL) {
                next = root->rightSibling;
                delete root;
                root = next;
            } else {
                next = root->father;
                delete root;
                root = next;
                while (root != NULL) {
                    if (root->rightSibling != NULL) {
                        next = root->rightSibling;
                        delete root;
                        root = next;
                        break;
                    }
                    next = root->father;
                    delete root;
                    root = next;
                }
            }
        }
    }
}

void __deleteNLTree(__NodeListTreeNode *root) {
    __NodeListTreeNode *cur = root->firstChild;

    __NodeListTreeNode *next = NULL;
    while (cur != NULL) {
        next = cur->next;
        __deleteNLTree(cur);
        cur = next;
    }
    delete root;
}

void __run(FILE *in, char* filename) {
    if (1 == dump) {
        __out = fopen("sdp_diffnodeset.txt", "wt");
        __result = new int[__numOfFItem];
        __resultLen = 0;
    }
    __buildTree(in, filename);
    __deleteFPTree();

    __nlRoot.label = __numOfFItem;
    __nlRoot.firstChild = NULL;
    __nlRoot.next = NULL;

    __initializeTree();
    __sameItems = new int[__numOfFItem];

    int from_cursor = __bf_cursor;
    int from_col = __bf_col;
    int from_size = __bf_currentSize;

    __NodeListTreeNode *curNode = __nlRoot.firstChild;
    __NodeListTreeNode *next = NULL;
    while (curNode != NULL) {
        next = curNode->next;
        __traverse(curNode, &__nlRoot, 1, 0);
        for (int c = __bf_col; c > from_col; c--)
            delete[] __buffer[c];
        __bf_col = from_col;
        __bf_cursor = from_cursor;
        __bf_currentSize = from_size;
        curNode = next;
    }

    delete []__item;
    delete[] __SupportDict;
    //YYY ???{
    delete[] __postOrderDict;
    //YYY ???}
    delete[] __sameItems;
    delete []__nlistBegin;
    delete []__nlistLen;

    //printf("-----%d %d %l \n", __nlNodeCount, __resultCount, __nlLenSum / ((double) __resultCount));
    cout<<__nlNodeCount<<" "<<__resultCount<<" "<<__nlLenSum / ((double) __resultCount)<<endl;
    
    
    if (1 == dump) {
        fclose(__out);
        delete []__result;
    }
}
//==========================================

int main(int argc, char **argv) {
    //cout << "usage: dFIN.exe <datafile> <MINSUP>(0~1)  <number_of_transactions> <ISOUT>\n";
    /*
     * <number_of_transactions> is not used here and there is for compability with
     * fp_growth and eclat implentations.
     * */
    char *filename = argv[1];
    double THRESHOLD = atof(argv[2]);
    dump = atoi(argv[4]);

    //--------------------- dFIN
    cout << "\ndFIN\n\t";
    __nlNodeCount = 0;
    __resultCount = 0;
    __nlLenSum = 0;
    __resultLen = 0;
    FILE *__in = NULL;
    __bf_size = 1000000;
    __buffer = new int*[100000];
    __bf_currentSize = __bf_size * 10;
    __buffer[0] = new int[__bf_currentSize];

    __bf_cursor = 0;
    __bf_col = 0;

    //Read Dataset
    __getData(__in, filename, THRESHOLD);
    __run(__in, filename);
    
    std::ofstream fout;
    fout.open ("orders.txt", std::ofstream::out | std::ofstream::app);
    fout<<"algorithm name\tminsup\tnumber of merges(k)\tlist1 length\tlist2 length\tlist1 length+list2 length\tkey operation in diff\t key operation in neg algorithm\n";
    fout<<filename<<"\t";
    fout<<THRESHOLD<<"\t";
    fout<<__number_of_merges<<"\t";
    fout<<1.0*__first_ns_Lenght/__number_of_merges<<"\t";
    fout<<1.0*__second_ns_length/__number_of_merges<<"\t";
    fout<<1.0*(__first_ns_Lenght+__second_ns_length)/__number_of_merges<<"\t";
    fout<<1.0*__sume_of_key_operation_in_diff_algorithm/__number_of_merges<<"\t";
    fout<<1.0*__sume_of_key_operation_in_neg_algorithm/__number_of_merges<<"\t\n";
    
  fout.close();
    
    cout<<"My Analysis: number of merges"<<__number_of_merges<<", avarage of key operation in diff"<<1.0*__sume_of_key_operation_in_diff_algorithm/__number_of_merges;
    cout<<", avarage of key operation in neg"<<1.0*__sume_of_key_operation_in_neg_algorithm/__number_of_merges<<endl;
    
    cout<<"avarage first"<<1.0*__first_ns_Lenght/__number_of_merges;
    cout<<", avarage second"<<1.0*__second_ns_length/__number_of_merges;
    cout<<", sum of fist and second"<<1.0*(__first_ns_Lenght+__second_ns_length)/__number_of_merges<<endl;
    return 0;
}

