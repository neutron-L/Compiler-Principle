#include <iostream>
#include <set>
#include <vector>
#include <stack>
#include <deque>
#include <queue>
#include <map>
#include <algorithm>
#include <iomanip>
using namespace std;

//定义LR(1)项目的结构体
struct LRProject {
    char left{}; //项目左部非终结符
    string right; //项目右部
    int dot{}; //原点位置
    set<char> reduceCh; //归约字符

    bool operator==(const LRProject &lrProject) const {
//        仅判断产生式是否相等
        return left == lrProject.left && right == lrProject.right
               && dot == lrProject.dot;
    }

    LRProject()=default;

    LRProject(char ch, string str, int d) : left{ch}, right{std::move(str)}, dot{d} {}

    void show() const {
        cout << "project:";
        cout << left << "->";
        for (int i = 0; i < right.length();) {
            if (i == dot)
                cout << "*";
            cout << right[i++];
        }
        if (dot == right.length())
            cout << "*";
        cout << ", ";
        for (auto it = reduceCh.begin(); it!= reduceCh.end(); it++) {
            if (it != reduceCh.begin())
                cout << '|';
            cout << *it;
        }
        cout << endl;
    }
};


//定义LR(1)项目集结构体
struct ItemSet{
    vector<LRProject> proSet; //保存该项目集中的LR(1)项目
    set<char> nextCh; //保存所有可以转移的符号
    int id{}; //对应DFA中的序号

    bool operator==(const ItemSet & itemSet) const {
        if (proSet.size() != itemSet.proSet.size())
            return false;
        for (auto &pro: itemSet.proSet) {
            auto findPro = find(proSet.begin(), proSet.end(), pro);
//            查找到对应的项目
            if (findPro == proSet.end())
                return false;
//            项目的归约字符也要相等
            for (auto &ch: findPro->reduceCh)
                if (!pro.reduceCh.count(ch))
                    return false;
        }
        return true;
    }

    void show() const {
        cout << "I"<<id<<":" <<endl;
        cout << "LRProjects:\n";
        for (auto &pro: proSet)
            pro.show();
        cout << "transfer character:\n";
        for (auto &ch: nextCh)
            cout << ch << ' ';
        cout << endl;
    }
};

LRProject start; //初始项目
ItemSet I; //开始状态
vector<ItemSet> C; //项目集规范族


//variable
deque<int> state; //状态栈
deque<char> symbol; //符号栈
deque<char> inputBuffer; //输入缓冲区 使用双端队列
map<pair<int, char>, pair<char, int>> action; //动作表 键为当前状态和输入符号，对应的值为
//操作  S: 转移状态 / R: 归约产生式
map<pair<int, char>, int> Goto; //状态转移表 根据状态栈顶和符号栈顶确定转移的状态

set<char> terminal, nonterminal; //终结符 非终结符集合
map<int, pair<char, string>> NumToProduction; //序号-产生式 用于移进归约时调用
map<pair<char, string>, int> ProductionToNum; //产生式-序号

map<char, vector<string>> production; //产生式左部-产生式右部 用于构建closure

map<char, set<char>> FIRST, FOLLOW; //FIRST FOLLOW集合


//process
void createFIRST(); //构造FIRST集合
void createFOLLOW(); //构造FOLLOW集合
void createClosure(ItemSet & item); //构造闭包
ItemSet go(ItemSet & item, char x); //go函数
void createLRCanonicalCollection(ItemSet & item); //构造项目集规范族
void showLROneTable(); //展示SLR(1)分析表
void LRAnalysisProcess(); //LR分析程序
void init(); //初始化函数  初始化各变量


/* 构造FIRST FOLLOW 集合
 */

void createFIRST(){
    bool flag;
    do{
        flag = false;
//        对于每一个非终结符
        for (auto& item: production) {
//            每一个产生式
            for (auto &p: item.second) {
//                如果产生式第一个是终结符 且目前未被加入
                if (terminal.count(p[0]) &&
                    !FIRST[item.first].count(p[0])) {
                    FIRST[item.first].insert(p[0]);
                    flag = true;
                }
//                如果是非终结符
                else {
                    for (auto &c: FIRST[p[0]]) {
                        if (!FIRST[item.first].count(c)) {
                            FIRST[item.first].insert(c);
                            flag = true;
                        }
                    }
                }
            }
        }
    }while (flag);
}

void createFOLLOW() {
    bool flag;

    FOLLOW['S'].insert('$');
    do {
        flag = false;
//        每一个非终结符
        for (auto &nt: nonterminal) {
//    每一个产生式
            for (auto &p: production[nt]) {
//                产生式 A->αBβ 把β的first集合加入B的follow集合
                for (int i = 0; i < p.size() - 1; i++) {
//                    如果β是非终结符
                    if (nonterminal.count(p[i + 1])) {
                        for (auto &f: FIRST[p[i + 1]]) {
                            if (!FOLLOW[p[i]].count(f)) {
                                FOLLOW[p[i]].insert(f);
                                flag = true;
                            }
                        }
                    } else {
                        if (!FOLLOW[p[i]].count(p[i + 1])) {
                            FOLLOW[p[i]].insert(p[i + 1]);
                            flag = true;
                        }
                    }
                }

//                产生式 A->αB 把A的follow集合加入B的follow集合 B为非终结符
                if (nonterminal.count(p.back())) {
                    for (auto &f: FOLLOW[nt])
                        if (!FOLLOW[p.back()].count(f)) {
                            FOLLOW[p.back()].insert(f);
                            flag = true;
                        }
                }
            }
        }
    } while (flag);
}


/*closure(I) 的构造过程
  *parameter: I: ItemSet
  *output: I
 */
void createClosure(ItemSet& item) {
    bool flag;
    do {
        flag = false;
//        每一个项目A->α*Bβ
        for (auto pro: item.proSet) {
//            每一个产生式B->β
            for (const auto &string: production[pro.right[pro.dot]]) {
//              获取项目 B->.β
                LRProject lrProject = LRProject(pro.right[pro.dot], string, 0);

//                如果β为空则把pro的归约符号集合加入新项目
                if (pro.dot + 1 == pro.right.length()) {
                    for (auto &ch: pro.reduceCh)
                        lrProject.reduceCh.insert(ch);
                }
//                如果β是终结符则把β加入新项目的归约符号集合
                else if (terminal.count(pro.right[pro.dot + 1]))
                    lrProject.reduceCh.insert(pro.right[pro.dot + 1]);
//                如果β是一个非终结符
                else
//                每一个b FIRST(βa)
                    for (auto &ch: FIRST[pro.right[pro.dot + 1]]) {
                        lrProject.reduceCh.insert(ch);
                    }

//                lrProject.show();

//                    如果是一个新项目  则加入
                if (find(item.proSet.begin(), item.proSet.end(), lrProject) == item.proSet.end()) {
                    item.proSet.push_back(lrProject);
                    flag = true;
                }

//                如果是老项目 则检查它们的归约字符集合
                else {
                    auto& findPro = *find(item.proSet.begin(), item.proSet.end(), lrProject);
                    for (auto &ch: lrProject.reduceCh)
                        if (!findPro.reduceCh.count(ch)) {
                            findPro.reduceCh.insert(ch);
                            flag = true;
                        }
                }
            }
        }
    } while (flag);
//    构造nextCh集合
    for (auto &pro: item.proSet)
        if (pro.dot < pro.right.length())
            item.nextCh.insert(pro.right[pro.dot]);
}

/*go转移函数
 * parameter: I: vector<LRProduction> x: char
 * output: J: vector<LRProduction>
 */

ItemSet go(ItemSet & item, char x) {
    ItemSet J;
    for (auto& pro: item.proSet){
        if (pro.right[pro.dot] == x) {
            LRProject newPro = pro;
            newPro.dot++;
            J.proSet.push_back(newPro);
        }
    }
    createClosure(J);

    return J;
}

/*构造文法项目集规范族
 * parameter: I: vector<LRProject> S`->.S
 * output: 项目集规范族C: vector<vector<LRProject>>
 *
 */

void createLRCanonicalCollection(ItemSet & item) {
    int id = 0;
    createClosure(item);
    item.id=id++;
    C.push_back(item);
    queue<ItemSet> que;
    que.push(item);


    while (!que.empty()) {
        auto nowitem = que.front();
        que.pop();

//            可以转移的字符
        for (auto &ch: nowitem.nextCh) {
            ItemSet J = go(nowitem, ch);
//                J非空
            if (!J.proSet.empty()) {
//                J未加入项目集规范族 则加入
                if (find(C.begin(), C.end(), J) == C.end()) {
                    J.id = id++;
                    que.push(J);
                    C.push_back(J);
                }

                // 找出J
                J = *find(C.begin(), C.end(), J);
//                    填写action/Goto表
//                    该字符是终结符 填入action表
                if (terminal.count(ch))
                    action[{nowitem.id, ch}] = {'S', J.id};

//                非终结符  填入goto表
                else
                    Goto[{nowitem.id, ch}] = J.id;
            }
        }
    }

    for (auto & itemSet: C){
        for (auto &pro: itemSet.proSet) {
//        如果是移进项目或者待约项目 即 dot < length 将移进字符保存

            if (pro.dot == pro.right.length()) {
//            接受项目
                if (pro.left == 'S' && pro.right == "E" &&
                pro.dot == 1 && pro.reduceCh.count('$')) {
                    for (auto &ch: FOLLOW[pro.left])
                        action[{itemSet.id, ch}] = {'A', 0};
                }
//            归约
                else {
                    for (auto &ch: pro.reduceCh)
                        action[{itemSet.id, ch}] = {'R', ProductionToNum[{pro.left, pro.right}]};
                }
            }
        }
    }
}

void test() {
/*
//    检查FIRST的构造
    createFIRST();
    createFOLLOW();

    cout << "  FIRST\t\tFOLLOW\n";
    for (auto &i: nonterminal) {
        cout << i <<": ";
        for (auto &j: FIRST[i])
            cout << j << ' ';
        cout << "\t\t";
        for (auto &j: FOLLOW[i])
            cout << j<<' ';
        cout << endl;
    }

//    检查FOLLOW的构造
     cout << "FOLLOW:\n";
    for (auto &i: nonterminal) {
        cout << i << ":";
        for (auto &j: FOLLOW[i])
            cout << j << ' ';
        cout << endl;
    }
    createFOLLOW();
    for (auto &i: nonterminal) {
        cout << i << ":";
        for (auto &j: FOLLOW[i])
            cout << j << ' ';
        cout << endl;
    }


    start = {'S', "E", 0};
    start.reduceCh.insert('$');
    ItemSet tmp;
    tmp.proSet.push_back(start);


//    测试createClosure go函数

    createClosure(tmp);
    cout << "start state:\n";
    tmp.show();

    auto nex = go(tmp, '(');
    cout << "start state input ):\n";
    nex.show();
*/
//
//    ItemSet J = go(I, 'E');
//    cout << "J:\n";
//    J.show();
//
//    ItemSet K = go(I, '(');
//    cout << "K:\n";
//    K.show();
//
//
////    测试为产生式标号
//    for (auto &item: ProductionToNum)
//        cout << item.second << ": " << item.first.first
//             << "->" << item.first.second << endl;
//
//
//
//
////    测试构建项目集规范族函数
//    createLRCanonicalCollection(I);
    for (auto& i: C) {
        i.show();
    }
////    检查action表
////    for(auto & item: action)
////        cout << item.first.first<< ' ' << item.first.second<< ' '<<item.second.first<<' '<<item.second.second<<endl;
////    检查goto表
//for(auto& item: Goto)
//    cout << item.first.first<<' ' << item.first.second<<' ' << item.second<<endl;
}

/*
 * 构造SLR(1)分析表
 *
 */
void showLROneTable() {
    cout << "\t\t\t action\t\t\t\t\t\t\tgoto\n";
    cout << "-------------------------------------------------------------------------------------------\n";
    cout << "state\t";
    for (auto &i: terminal)
        cout << i << '\t';
    for (auto &i: nonterminal)
        if (i != 'S')
            cout << i << '\t';
    cout << endl;

    for (int i = 0; i < C.size(); i++) {
        cout << "-------------------------------------------------------------------------------------------\n";
        cout << i << '\t';
        for (auto &ch: terminal) {
            if (action.count({i, ch}))
                cout << action[{i, ch}].first << action[{i, ch}].second << "\t";
            else
                cout << "\t";
        }
        for (auto &ch: nonterminal) {
            if (ch != 'S') {
                if (Goto.count({i, ch}))
                    cout << Goto[{i, ch}] << '\t';
                else
                    cout << '\t';
            }
        }
        cout << endl;
    }
    cout << "-------------------------------------------------------------------------------------------\n";
}

/*
 * LR分析程序
 */

void LRAnalysisProcess() {
    bool flag = true;
    state.push_back(0);
    symbol.push_back('-');
    int len;
    int blanks = inputBuffer.size() * 3 /2;

    cout << "Analysis Process:\n";
    cout
            << "----------------------------------------------------------------------------------------------------------\n";
    cout << " stack\t\t\t\t\t\t\t\tinput\t\t\tAnalysis action" << endl;
    cout
            << "----------------------------------------------------------------------------------------------------------\n";

    do {
//        展示当前分析情况
//栈
        cout << " State: ";
        for (auto &item: state)
            cout << setw(3) << item;
        cout << endl;
        cout << "Symbol: ";
        for (auto &item: symbol)
            cout << setw(3) << item;
        len = 3 * (blanks - symbol.size() - inputBuffer.size());
        while (len--)
            cout << ' ';

        for (auto &item: inputBuffer)
            cout << setw(3) << item;

        cout << "\t\t\t";


//        s是state栈顶状态 a是ip所指向的符号
        int s = state.back();
        char a = inputBuffer.front();
        switch (action[{s, a}].first) {
            case 'S': {
                cout << "Shift " << action[{s, a}].second;
//             把a和 shift s`压入symbol栈和state栈
                symbol.push_back(a);
                state.push_back(action[{s, a}].second);
//            指针前移
                inputBuffer.pop_front();
            }
                break;
            case 'R': {
//                取出归约式
                int number = action[{s, a}].second;
                auto p = NumToProduction[number];
//                弹出|β|个字符
                int sz = p.second.size();
                while (sz--) {
                    symbol.pop_back();
                    state.pop_back();
                }
                symbol.push_back(p.first);
                state.push_back(Goto[{state.back(), symbol.back()}]);
                cout << "reduce by " << p.first << "->" << p.second;
            }
                break;
            case 'A': {
                cout << "ACC";
                flag = false;
            }
                break;
//            出错
            default: {
                flag = false;
                cout << "error";
            }
                break;
        }
        cout << endl;
        cout
                << "----------------------------------------------------------------------------------------------------------\n";
    } while (flag);
}


void init() {
//    初始化终结符集合
    terminal.insert('+');
    terminal.insert('-');
    terminal.insert('*');
    terminal.insert('/');
    terminal.insert('(');
    terminal.insert(')');
    terminal.insert('n');
    terminal.insert('$');

//    初始化非终结符集合
    nonterminal.insert('E');
    nonterminal.insert('S');
    nonterminal.insert('T');
    nonterminal.insert('F');


//    产生式左右对应map初始化
    production['S'] = {"E"};
    production['E'] = {"E+T", "E-T", "T"};
    production['T'] = {"T*F", "T/F", "F"};
    production['F'] = {"(E)", "n"};

//    产生式-序号  序号-产生式初始化

    int id = 1;
    for (auto &left: nonterminal)
        for (auto &p: production[left]) {
            ProductionToNum[{left, p}] = id++;
            NumToProduction[id - 1] = {left, p};
        }
}

int main() {
    init();

    start = {'S', "E", 0};
    start.reduceCh.insert('$');
    I.proSet.push_back(start);

    createFIRST();
    createFOLLOW();
    createLRCanonicalCollection(I);


//    test();

    showLROneTable();


 //    输入串存入缓冲区
    cout << "Enter the string:";
    string str;
    cin >> str;
    for (auto & ch: str)
        inputBuffer.push_back(ch);
    inputBuffer.push_back('$');
//   分析过程
    LRAnalysisProcess();

    return 0;
}
