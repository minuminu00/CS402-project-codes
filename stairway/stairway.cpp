#include <bits/stdc++.h>
using namespace std;

struct Trie{
    bool finish;
    Trie* next[10];

    Trie() : finish(false) {
        memset(next, 0, sizeof(next));
    }
    ~Trie() {
        for (int i=0; i<10; i++){
            if(next[i]){
                delete next[i];
            }
        }
    }
    void insert(vector<int> &key, int idx){
        if(idx == key.size()){
            finish = true;
        }
        else{
            int curr = key[idx];
            if(!next[curr]){
                next[curr] = new Trie();
            }
            next[curr]->insert(key, idx+1);
        }
    }
    Trie* find(vector<int> &key, int idx){
        if(idx == key.size()){
            if(finish){
                return this;
            }
            else{
                return NULL;
            }
        }
        int curr = key[idx];
        if(!next[curr]){
            return NULL;
        }
        return next[curr]->find(key, idx+1);
    }
};

vector<int> rule(int s, vector<int> &L1, vector<int> &L2){
    vector<int> L3, L4, L5;
    int idx1 = 0, idx2 = 0;
    int N1 = L1.size(), N2 = L2.size();
    int x = max(N1+N2-s, 0);
    for(int i=0; i<x; i++){
        if(idx1 == N1-1){
            L3.push_back(L2[idx2++]);
        }
        else if(idx2 == N2-1 || L1[idx1] < L2[idx2]){
            L3.push_back(L1[idx1++]);
        }
        else{
            L3.push_back(L2[idx2++]);
        }
    }
    while(true){
        if(idx1 == N1){
            if(idx2 == N2){
                break;
            }
            L4.push_back(L2[idx2++]-1);
        }
        else if(idx2 == N2 || L1[idx1] < L2[idx2]){
            L4.push_back(L1[idx1++]-1);
        }
        else{
            L4.push_back(L2[idx2++]-1);
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
                return L5;
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

void printStair(FILE* fp, vector<int> &stair){
    int N = stair.size();
    fprintf(fp, "{");
    for(int i=0; i<N; i++){
        fprintf(fp, "%d", stair[i]);
        if(i!=N-1){
            fprintf(fp, ", ");
        }
    }
    fprintf(fp, "}");
}

bool dominate(vector<int> &stair1, vector<int> &stair2){
    int N1 = stair1.size(), N2 = stair2.size();
    int N = min(N1, N2);
    int S;
    for(int i=1; i<=N; i++){
        S += (stair1[N1-i] - stair2[N2-i]);
        if(S < 0){
            return false;
        }
    }
    if(N1 < N2){
        for(int i=N1+1; i<=N2; i++){
            S -= stair2[N2-i];
        }
    }
    return S >= 0;
}

int main(void){
    int S = 4;
    for(int K=3; ; K++){
        clock_t start_time, end_time, start_time_, end_time_;
        start_time = clock();
        for( ; ; S++){
            start_time_ = clock();
            printf("TRYING: %d %d\n", K, S);
            bool unsat = false;
            vector<pair<vector<int>, pair<int, int> > > A;
            vector<bool> validIdx;
            queue<pair<vector<int>, pair<int, int> > > Q;
            Trie visited = Trie(); 
            Q.push({{K}, {-1, -1}});

            while(!Q.empty()){
                auto front = Q.front();
                vector<int> currStair = front.first;
                Q.pop();
                int currIdx = A.size();
                A.push_back(front);
                validIdx.push_back(true);
                if(currStair.empty()){
                    unsat = true;
                    break;
                }
                for(int i=0; i<A.size(); i++){
                    if(validIdx[i]){
                        vector<int> otherStair = A[i].first;
                        if(i!=A.size()-1){
                            if(dominate(currStair, otherStair)){
                                validIdx[A.size()-1] = false;
                                break;
                            }
                            if(dominate(otherStair, currStair)){
                                validIdx[i] = false;
                                continue;
                            }
                        }
                        vector<int> newStair = rule(S, currStair, otherStair);
                        if(newStair.size() < S && !visited.find(newStair, 0)){
                            visited.insert(newStair, 0);
                            Q.push({newStair, {i, currIdx}});
                        }
                    }
                }
            }
            end_time_ = clock();
            printf("Elapsed time: %.2lf seconds\n", (double)(end_time_-start_time_) / CLOCKS_PER_SEC);

            if(unsat){
                end_time = clock();
                char filename[30];
                sprintf(filename, "results/stairway-%d.txt", K);
                FILE *fp = fopen(filename, "w");
                fprintf(fp, "f1(%d) = %d\n", K, S-1);
                fprintf(fp, "Elapsed time: %.2lf seconds\n", (double)(end_time-start_time) / CLOCKS_PER_SEC);
                queue<pair<vector<int>, pair<int, int> > > track;
                set<int> visitedIdx;
                track.push(A[A.size()-1 ]);
                visitedIdx.insert(A.size()-1);
                while(!track.empty()){
                    auto L = track.front();
                    track.pop();
                    vector<int> curr = L.first;
                    int idx1 = L.second.first, idx2 = L.second.second;
                    if(idx1 != -1){
                        printStair(fp, curr);
                        fprintf(fp, " = ");
                        printStair(fp, A[idx1].first);
                        fprintf(fp, " ++ ");
                        if(visitedIdx.find(idx1) == visitedIdx.end()){
                            track.push(A[idx1]);
                            visitedIdx.insert(idx1);
                        }
                        printStair(fp, A[idx2].first);
                        if(visitedIdx.find(idx2) == visitedIdx.end()){
                            track.push(A[idx2]);
                            visitedIdx.insert(idx2);
                        }
                        fprintf(fp, "\n");
                    }
                }
                fclose(fp);
                break;
            }
        }
    }

}