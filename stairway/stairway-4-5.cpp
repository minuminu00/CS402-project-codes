#include <bits/stdc++.h>
using namespace std;

int K = 4, S = 5;

struct Trie{
    Trie* next[10];
    int val;

    Trie() : val(0) {
        memset(next, 0, sizeof(next));
    }
    ~Trie() {
        for (int i=0; i<10; i++){
            if(next[i]){
                delete next[i];
            }
        }
    }
    void insert(vector<int> &key, int idx, int _val){
        if(idx == key.size()){
            val = _val;
        }
        else{
            int curr = key[idx];
            if(!next[curr]){
                next[curr] = new Trie();
            }
            next[curr]->insert(key, idx+1, _val);
        }
    }
    int find(vector<int> &key, int idx){
        if(idx == key.size()){
            if(val){
                return val;
            }
            else{
                return 100000;
            }
        }
        int curr = key[idx];
        if(!next[curr]){
            return 100000;
        }
        return next[curr]->find(key, idx+1);
    }
};

class Stairway{
public:
    vector<int> L;
    int idx1;
    int idx2;
    int num_clauses;

    Stairway(vector<int> n_L, int n_idx1, int n_idx2, int n_num_clauses){
        L = n_L;
        idx1 = n_idx1;
        idx2 = n_idx2;
        num_clauses = n_num_clauses;
    }
};

vector<Stairway> A;

struct compare{
    bool operator()(const int& x, const int& y)const{
        return A[x].num_clauses > A[y].num_clauses;
    }
};

priority_queue<int, vector<int>, compare> Q;

Stairway rule(int n1, int n2, int s1, int s2){
    vector<int> L3, L4, L5;
    int idx1 = 0, idx2 = 0;
    int N1 = A[s1].L.size(), N2 = A[s2].L.size();
    int x = max(N1+N2-n1-n2, 0);
    for(int i=0; i<x; i++){
        if(idx1 == N1-n1){
            L3.push_back(A[s2].L[idx2++]);
        }
        else if(idx2 == N2-n2 || A[s1].L[idx1] < A[s2].L[idx2]){
            L3.push_back(A[s1].L[idx1++]);
        }
        else{
            L3.push_back(A[s2].L[idx2++]);
        }
    }
    while(true){
        if(idx1 == N1){
            if(idx2 == N2){
                break;
            }
            L4.push_back(A[s2].L[idx2++]-1);
        }
        else if(idx2 == N2 || A[s1].L[idx1] < A[s2].L[idx2]){
            L4.push_back(A[s1].L[idx1++]-1);
        }
        else{
            L4.push_back(A[s2].L[idx2++]-1);
        }
    }
    int idx3 = 0, idx4 = 0;
    int N3 = L3.size(), N4 = L4.size();
    while(idx3 != N3 && !L3[idx3]){
        idx3++;
    }
    while(idx4 != N4 && !L4[idx4]){
        idx4++;
    }
    while(true){
        if(idx3 == N3){
            if(idx4 == N4){
                return Stairway(L5, s1, s2, A[s1].num_clauses + A[s2].num_clauses);
            }
            L5.push_back(L4[idx4++]);
        }
        else if(idx4 == N4 || L3[idx3] < L4[idx4]){
            L5.push_back(L3[idx3++]);
        }
        else{
            L5.push_back(L4[idx4++]);
        }
    }
}

void printStair(FILE* fp, int st){
    int N = A[st].L.size();
    fprintf(fp, "{");
    for(int i=0; i<N; i++){
        fprintf(fp, "%d", A[st].L[i]);
        if(i!=N-1){
            fprintf(fp, ", ");
        }
    }
    fprintf(fp, "} (%d)", A[st].num_clauses);
}

int main(void){
    clock_t start_time, end_time, start_time_, end_time_;
    start_time = clock();
    start_time_ = clock();
    Trie visited = Trie(); 
    A.push_back(Stairway({K}, -1, -1, 1));
    int leaf = 0;
    Q.push(0);

    while(!Q.empty()){
        int currStair = Q.top();
        Q.pop();
        if(A[currStair].L.empty()){
            leaf = currStair;
            break;
        }
        if(A[currStair].num_clauses > visited.find(A[currStair].L, 0)){
            continue;
        }
        visited.insert(A[currStair].L, 0, -1);

        for(int otherStair = 0; otherStair <= currStair; otherStair++){
            for(int s1 = 1; s1 < S && s1 <= A[currStair].L.size(); s1++){
                for(int s2 = 1; s1+s2 <= S && s2 <= A[otherStair].L.size(); s2++){
                    Stairway newStair = rule(s1, s2, currStair, otherStair);
                    if(newStair.L.size() < S && newStair.num_clauses < visited.find(newStair.L, 0)){
                        A.push_back(newStair);
                        visited.insert(newStair.L, 0, newStair.num_clauses);
                        Q.push(A.size()-1);
                    }
                }
            }
            
        }
    }
    end_time_ = clock();
    printf("Elapsed time: %.2lf seconds\n", (double)(end_time_-start_time_) / CLOCKS_PER_SEC);

    if(leaf){
        end_time = clock();
        char filename[30];
        sprintf(filename, "results-4-5/stairway.txt");
        FILE *fp = fopen(filename, "w");
        fprintf(fp, "f1(%d) = %d\n", K, S-1);
        fprintf(fp, "Elapsed time: %.2lf seconds\n", (double)(end_time-start_time) / CLOCKS_PER_SEC);
        queue<int> track;
        set<int> visitedIdx;
        track.push(leaf);
        visitedIdx.insert(leaf);
        while(!track.empty()){
            int curr = track.front();
            track.pop();
            int idx1 = A[curr].idx1;
            int idx2 = A[curr].idx2;
            if(idx1!=-1){
                printStair(fp, curr);
                fprintf(fp, " = ");
                printStair(fp, idx1);
                fprintf(fp, " ++ ");
                if(visitedIdx.find(idx1) == visitedIdx.end()){
                    track.push(idx1);
                    visitedIdx.insert(idx1);
                }
                printStair(fp, idx2);
                if(visitedIdx.find(idx2) == visitedIdx.end()){
                    track.push(idx2);
                    visitedIdx.insert(idx2);
                }
                fprintf(fp, "\n");
            }
        }
        fclose(fp);
    }

}