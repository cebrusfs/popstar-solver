// @author cebrusfs
// headers {{{
#include<cstdlib>
#include<cmath>
#include<cassert>
#include<cstring>

#include<iostream>
#include<algorithm>
#include<array>
#include<map>
#include<set>
#include<vector>
#include<unordered_map>
#include<unordered_set>
#include<functional>
using namespace std;
// }}}
// macros {{{
#define ALL(x) (x).begin(), (x).end()
#define SZ(x) ((int)(x).size())
#define UNIQUE(x) (sort(ALL(x)), ((x).erase(unique(ALL(x)), (x).end())))
#define MSA(x, v) std::fill(ALL(x), (v))
#define MS(st, ed, v) std::fill((st), (ed), (v))

#define REP(i,n) for(int i=0;i<(n);i++)
#define REP1(i,a,b) for(int i=(a);i<=(b);i++)

#define PER(i,n) for(int i=(n)-1;i>=0;i--)
#define PER1(i,a,b) for(int i=(a);i>=(b);i--)

typedef unsigned int uint;
typedef long long ll;
typedef unsigned long long ull;
typedef long double ld;

typedef pair<int, int> PII;
#define MP make_pair
#define F first
#define S second

typedef vector<int> VI;
#define PB push_back
#define PF push_front

#define PPB pop_back
#define PPF pop_front

#define runtime() ((double)clock() / CLOCKS_PER_SEC)

const double eps = 1e-7;

// C++11
#if __cplusplus >= 201103L
#define MT make_tuple
typedef tuple<int, int> TII;

// dump() {{{
template<typename Iter>
ostream& _out(ostream &s, Iter b, Iter e) {
    s << "[";
    for (auto it = b; it != e; it++) s << (it == b ? "":" ") << *it;
    s << "]";
    return s;
}

template<typename A, typename B>
ostream& operator <<(ostream &s, const pair<A,B> &p) { return s<<"("<<p.first<<","<<p.second<<")"; }
template<typename T>
ostream& operator <<(ostream &s, const vector<T> &c) { return _out(s,ALL(c)); }
template<typename T>
ostream& operator <<(ostream &s, const set<T> &c) { return _out(s,ALL(c)); }
template<typename T>
ostream& operator <<(ostream &s, const unordered_set<T> &c) { return _out(s,ALL(c)); }
template<typename A, typename B>
ostream& operator <<(ostream &s, const map<A,B> &c) { return _out(s,ALL(c)); }
template<typename A, typename B>
ostream& operator <<(ostream &s, const unordered_map<A,B> &c) { return _out(s,ALL(c)); }

template<typename T>
void _dump(const char* s, T&& head) {
    cerr << s << "=" << head << endl;
}

template<typename T, typename... Args>
void _dump(const char* s, T&& head, Args&&... tail) {
    int c = 0;
    while (*s!=',' || c!=0) {
        if (*s=='(' || *s=='[' || *s=='{') c++;
        if (*s==')' || *s==']' || *s=='}') c--;
        cerr << *s++;
    }
    cerr << "=" << head << ", ";
    _dump(s+1, tail...);
}

#ifdef FISH
#define dump(...) do { \
    fprintf(stderr, "%s:%d - ", __PRETTY_FUNCTION__, __LINE__); \
    _dump(#__VA_ARGS__, __VA_ARGS__); \
} while (0);
#else
#define dump(...) ;
#endif
// }}}

#endif
// }}}

#define MAX 10
#define COLOR_MAX 5

// Bonus = 2000 - Blocks^2 * 20
// score = block^2 * 5

const char COLOR_SYMBOL[] = ".rgbyp";
const int COLOR2ASCII[] = {40, 41, 42, 44, 43, 45};

const int EMPTY = 0;

const int DIRATIONS[4][2] = {{1, 0}, {-1, 0}, {0, 1}, {0, -1}};

typedef vector<int> GROUP;
typedef pair<int, GROUP> COLOR_GROUP;
#define PACK(x, y) ((x) * 128 + (y))
#define FST(x) ((x) / 128)
#define SND(x) ((x) % 128)

typedef pair<long long, long long> HASH;

inline bool move_down(char col[])
{
    int real_r = MAX - 1;

    for (int r = MAX - 1; r >= 0; --r)
        if (col[r] != EMPTY)
            col[real_r--] = col[r];
    for (int r = real_r; r >= 0; --r)
        col[r] = EMPTY;

    // return true if empty column
    return real_r == MAX - 1;
}

class Game {
  public:
    int step;

    array<GROUP, MAX*MAX> global_best_actions;
    int global_best_score;
    bool global_changed;

  private:
    char raw[MAX*MAX][MAX][MAX];

    char (*mp)[MAX];

    GROUP actions[MAX*MAX];
    int history_score[MAX*MAX];

  public:
    Game () {
        step = 0;
        mp = NULL;
        history_score[0] = 0;
        global_best_score = 0;
        global_changed = true;
    }

    /*
     * Input
     */
    void generate()
    {
        printf("[*] Get random map\n");

        step = 0;
        for (int r = 0; r < MAX; ++r)
            for (int c = 0; c < MAX; ++c)
                raw[0][c][r] = 1 + rand() % COLOR_MAX;

        init();
    }
    void stdin_input()
    {
        printf("[*] Get map from stdin\n");
        FILE* f = stdin;
        assert(f != NULL);
        parse_input(f);
    }
    void file_input(char filename[])
    {
        printf("[*] Get map from file: %s\n", filename);
        FILE* f = fopen(filename, "r");
        assert(f != NULL);
        parse_input(f);
        fclose(f);
    }


    int currect_score() const
    {
        return history_score[step];
    }

    int eliminate(const GROUP& group)
    {
        bool used[MAX];
        memset(used, false, sizeof(used));

        int add = group.size() * group.size() * 5;

        for (const auto& p : group)
            used[FST(p)] = true;

        static_assert(sizeof(raw[step]) == MAX * MAX * sizeof(char));
        memcpy(raw[step + 1], raw[step], sizeof(raw[step]));

        // copied, and step forward!
        actions[step] = group;
        history_score[step + 1] = currect_score() + add;
        step += 1;
        mp = raw[step];

        // eliminate on new copy
        for (const auto& p : group)
            mp[FST(p)][SND(p)] = EMPTY;

        bool is_empty[MAX];
        memset(is_empty, false, sizeof(is_empty));
        for (int c = 0; c < MAX; ++c)
            is_empty[c] = move_down(mp[c]);

        // move down & move left
        int real_c = 0;
        char* empty_col = NULL;
        for (int c = 0; c < MAX; ++c)
        {
            if (used[c] and is_empty[c])
                empty_col = mp[c];
            else
                //mp[real_c++] = mp[c];
                //static_assert(sizeof(char) * MAX == sizeof(mp[c]));
                memcpy(mp[real_c++], mp[c], sizeof(mp[c]));
        }
        assert((real_c < MAX and empty_col != NULL) or real_c == MAX);
        for (int c = real_c; c < MAX; ++c)
            //mp[c] = empty_col;
            //static_assert(sizeof(char) * MAX == sizeof(mp[c]));
            memset(mp[c], 0, sizeof(char) * MAX);

        return add;
    }

    void recover(int to_step)
    {
        step = to_step;
        mp = raw[step];
    }

    void pretty_print(const GROUP &g = GROUP()) const
    {
        printf("  ");
        for (int c = 0; c < MAX; ++c)
            printf("%-2d", c);
        printf("\n");

        for (int r = 0; r < MAX; ++r)
        {
            printf("%-2d", r);
            for (int c = 0; c < MAX; ++c)
            {
                bool choosed = false;
                for (const auto& idx : g)
                    if (FST(idx) == c and SND(idx) == r)
                        choosed = true;

                int color = COLOR2ASCII[(int) mp[c][r]];

                printf("\x1b[1;%dm%s\x1b[m", color, choosed ? ".." : "  ");
            }
            printf("\n");
        }
    }

    int cal_end() const
    {
        int cnt = 0;
        for (int i = 0; i < MAX; ++i)
            for (int j = 0; j < MAX; ++j)
                if (mp[i][j] != EMPTY)
                    cnt ++;
        return max(2000 - cnt * cnt * 20, 0);
    }

    // bfs
    GROUP bfs(int x, int y) const
    {
        bool vis[MAX][MAX];
        memset(vis, false, sizeof(vis));

        GROUP q;
        q.reserve(32);

        int fd = 0;
        q.emplace_back(PACK(x, y));
        vis[x][y] = false;

        while (fd < (int)q.size())
        {
            const auto& p = q[fd++];

            for (int d = 0; d < 4; ++d)
            {
                int a = FST(p) + DIRATIONS[d][0];
                int b = SND(p) + DIRATIONS[d][1];

                if (0 <= a and a < MAX and 0 <= b and b < MAX
                    and not vis[a][b] and mp[x][y] == mp[a][b])
                {
                    vis[a][b] = true;
                    q.emplace_back(PACK(a, b));
                }
            }
        }
        return q;
    }


  private:
    void init()
    {
        step = 0;
        /*
        for (int c = 0; c < MAX; ++c)
            history[0][c] = raw[0][c];

        mp = history[0];
        */
        mp = raw[0];
    }

    void parse_input(FILE* f)
    {
        for (int r = 0; r < MAX; ++r)
            for (int c = 0; c < MAX; ++c)
            {
                char ch;
                int ret = fscanf(f, " %c", &ch);
                assert(ret == 1);
                auto ptr = strchr(COLOR_SYMBOL, ch);

                if (ptr == NULL)
                {
                    printf("char: %c (%d)\n", ch, ch);
                    assert(false);
                }
                raw[0][c][r] = ptr - COLOR_SYMBOL;
            }

        init();
    }

};


int main(int argc, char *argv[])
{
    Game game;

    if (argc == 2)
    {
        if (strcmp(argv[1], "-") == 0)
        {
            game.stdin_input();
        }
        else
        {
            game.file_input(argv[1]);
        }
    }
    else
    {
        srand(514514);
        game.generate();
    }

    srand(time(NULL));

    /*
     * start
     */

    while (true)
    {
        int r, c;

        printf(
            "---------------------\n"
            "Step %d: score %d\n",
            game.step,
            game.currect_score()
        );
        game.pretty_print();

        printf("\n> ");
        scanf("%d", &r);
        if (r == -1)
        {
            game.recover(game.step - 1);
            continue;
        }
        scanf("%d", &c);

        auto action = game.bfs(c, r);
        game.pretty_print(action);
        game.eliminate(action);
    }

    int score = game.currect_score() + game.cal_end();
    printf("End Step %d: %d\n", game.step, score);
}

