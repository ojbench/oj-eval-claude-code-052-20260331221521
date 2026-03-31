#include <iostream>
#include <algorithm>
#include <cstring>
#include <string>
#include <cctype>

using namespace std;

class term {
public:
    int a, b, c, d;

    term() : a(0), b(0), c(0), d(0) {}
    term(int _a, int _b, int _c, int _d) : a(_a), b(_b), c(_c), d(_d) {}

    bool operator == (const term &obj) const {
        return b == obj.b && c == obj.c && d == obj.d;
    }

    bool operator != (const term &obj) const {
        return b != obj.b || c != obj.c || d != obj.d;
    }

    bool operator < (const term &obj) const {
        if (b != obj.b) return b > obj.b;
        if (c != obj.c) return c > obj.c;
        return d > obj.d;
    }
};

class poly {
public:
    int n;
    term *t;

    poly() : n(0), t(NULL) {}

    poly(int _n) {
        n = _n;
        t = new term[n];
    }

    poly(const poly &p) {
        n = p.n;
        t = new term[n];
        for (int i = 0; i < n; ++i) {
            t[i] = p.t[i];
        }
    }

    void simplify() {
        if (n == 0) return;

        // Sort terms
        sort(t, t + n);

        // Combine like terms
        int write = 0;
        for (int read = 0; read < n; ++read) {
            if (write > 0 && t[write - 1] == t[read]) {
                t[write - 1].a += t[read].a;
            } else {
                t[write++] = t[read];
            }
        }

        // Remove zero terms
        int newN = 0;
        for (int i = 0; i < write; ++i) {
            if (t[i].a != 0) {
                t[newN++] = t[i];
            }
        }
        n = newN;
    }

    poly operator + (const poly &obj) const {
        poly ans(n + obj.n);
        for (int i = 0; i < n; ++i) ans.t[i] = t[i];
        for (int i = 0; i < obj.n; ++i) ans.t[i + n] = obj.t[i];
        ans.simplify();
        return ans;
    }

    poly operator - (const poly &obj) const {
        poly ans(n + obj.n);
        for (int i = 0; i < n; ++i) ans.t[i] = t[i];
        for (int i = 0; i < obj.n; ++i) {
            ans.t[i + n] = obj.t[i];
            ans.t[i + n].a *= -1;
        }
        ans.simplify();
        return ans;
    }

    poly operator * (const poly &obj) const {
        poly ans(n * obj.n);
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < obj.n; ++j) {
                ans.t[i * obj.n + j].a = t[i].a * obj.t[j].a;
                ans.t[i * obj.n + j].b = t[i].b + obj.t[j].b;
                ans.t[i * obj.n + j].c = t[i].c + obj.t[j].c;
                ans.t[i * obj.n + j].d = t[i].d + obj.t[j].d;
            }
        }
        ans.simplify();
        return ans;
    }

    poly& operator = (const poly &obj) {
        if (&obj == this) return *this;
        n = obj.n;
        if (t != NULL) delete []t;
        t = new term[n];
        for (int i = 0; i < n; ++i) {
            t[i] = obj.t[i];
        }
        return *this;
    }

    poly derivate() const {
        poly ans(n * 3);  // Maximum possible terms after derivation
        int idx = 0;

        for (int i = 0; i < n; ++i) {
            // Derivative of x^b term
            if (t[i].b > 0) {
                ans.t[idx].a = t[i].a * t[i].b;
                ans.t[idx].b = t[i].b - 1;
                ans.t[idx].c = t[i].c;
                ans.t[idx].d = t[i].d;
                idx++;
            }

            // Derivative of sin^c term
            if (t[i].c > 0) {
                ans.t[idx].a = t[i].a * t[i].c;
                ans.t[idx].b = t[i].b;
                ans.t[idx].c = t[i].c - 1;
                ans.t[idx].d = t[i].d + 1;
                idx++;
            }

            // Derivative of cos^d term
            if (t[i].d > 0) {
                ans.t[idx].a = -t[i].a * t[i].d;
                ans.t[idx].b = t[i].b;
                ans.t[idx].c = t[i].c + 1;
                ans.t[idx].d = t[i].d - 1;
                idx++;
            }
        }

        ans.n = idx;
        ans.simplify();
        return ans;
    }

    ~poly() {
        if (t != NULL) delete []t;
    }
};

class frac {
public:
    poly p, q;

    frac() {}

    frac(int x) {
        p = poly(1);
        p.t[0] = term(x, 0, 0, 0);
        q = poly(1);
        q.t[0] = term(1, 0, 0, 0);
    }

    frac(term _p) {
        q = poly(1);
        q.t[0] = term(1, 0, 0, 0);
        p = poly(1);
        p.t[0] = _p;
    }

    frac(poly _p, poly _q) : p(_p), q(_q) {}

    frac operator + (const frac &obj) const {
        return frac(p * obj.q + q * obj.p, q * obj.q);
    }

    frac operator - (const frac &obj) const {
        return frac(p * obj.q - q * obj.p, q * obj.q);
    }

    frac operator * (const frac &obj) const {
        return frac(p * obj.p, q * obj.q);
    }

    frac operator / (const frac &obj) const {
        return frac(p * obj.q, q * obj.p);
    }

    frac derivate() const {
        poly dp = p.derivate();
        poly dq = q.derivate();
        return frac(dp * q - dq * p, q * q);
    }

    void output() {
        // Handle special case: numerator is 0
        if (p.n == 0) {
            cout << "0";
            return;
        }

        // Check if denominator is 1
        bool denomIs1 = (q.n == 1 && q.t[0].a == 1 && q.t[0].b == 0 &&
                         q.t[0].c == 0 && q.t[0].d == 0);

        // Output numerator
        bool needParens = (p.n > 1) && !denomIs1;
        if (needParens) cout << "(";

        for (int i = 0; i < p.n; ++i) {
            int coef = p.t[i].a;
            int xpow = p.t[i].b;
            int sinpow = p.t[i].c;
            int cospow = p.t[i].d;

            // Handle sign and coefficient
            bool isConst = (xpow == 0 && sinpow == 0 && cospow == 0);

            if (i == 0) {
                if (coef < 0) {
                    cout << "-";
                    if (isConst || abs(coef) != 1) cout << abs(coef);
                } else {
                    if (isConst || abs(coef) != 1) cout << coef;
                }
            } else {
                if (coef < 0) {
                    cout << "-";
                    if (isConst || abs(coef) != 1) cout << abs(coef);
                } else {
                    cout << "+";
                    if (isConst || abs(coef) != 1) cout << coef;
                }
            }

            // Output x power
            if (xpow > 0) {
                cout << "x";
                if (xpow > 1) cout << "^" << xpow;
            }

            // Output sin power
            if (sinpow > 0) {
                cout << "sin";
                if (sinpow > 1) cout << "^" << sinpow;
                cout << "x";
            }

            // Output cos power
            if (cospow > 0) {
                cout << "cos";
                if (cospow > 1) cout << "^" << cospow;
                cout << "x";
            }
        }

        if (needParens) cout << ")";

        // Output denominator if not 1
        if (!denomIs1) {
            cout << "/";

            bool denomNeedParens = (q.n > 1);
            if (denomNeedParens) cout << "(";

            for (int i = 0; i < q.n; ++i) {
                int coef = q.t[i].a;
                int xpow = q.t[i].b;
                int sinpow = q.t[i].c;
                int cospow = q.t[i].d;

                bool isConst = (xpow == 0 && sinpow == 0 && cospow == 0);

                if (i == 0) {
                    if (coef < 0) {
                        cout << "-";
                        if (isConst || abs(coef) != 1) cout << abs(coef);
                    } else {
                        if (isConst || abs(coef) != 1) cout << coef;
                    }
                } else {
                    if (coef < 0) {
                        cout << "-";
                        if (isConst || abs(coef) != 1) cout << abs(coef);
                    } else {
                        cout << "+";
                        if (isConst || abs(coef) != 1) cout << coef;
                    }
                }

                if (xpow > 0) {
                    cout << "x";
                    if (xpow > 1) cout << "^" << xpow;
                }

                if (sinpow > 0) {
                    cout << "sin";
                    if (sinpow > 1) cout << "^" << sinpow;
                    cout << "x";
                }

                if (cospow > 0) {
                    cout << "cos";
                    if (cospow > 1) cout << "^" << cospow;
                    cout << "x";
                }
            }

            if (denomNeedParens) cout << ")";
        }
    }
};

// Parser
int pos;
char *str;
int len;

frac parseExpr();
frac parseTerm();
frac parseFactor();

int readInt() {
    int val = 0;
    while (pos < len && isdigit(str[pos])) {
        val = val * 10 + (str[pos] - '0');
        pos++;
    }
    return val;
}

term parseSingleTerm() {
    int coef = 1;
    int xpow = 0, sinpow = 0, cospow = 0;
    bool hasCoef = false;

    // Check for coefficient
    if (pos < len && isdigit(str[pos])) {
        coef = readInt();
        hasCoef = true;
    }

    // Parse x, sinx, cosx in sequence
    while (pos < len) {
        if (str[pos] == 'x') {
            pos++;
            if (pos < len && str[pos] == '^') {
                pos++;
                xpow = readInt();
            } else {
                xpow = 1;
            }
        } else if (pos + 3 <= len && str[pos] == 's' && str[pos+1] == 'i' &&
                   str[pos+2] == 'n') {
            pos += 3;
            if (pos < len && str[pos] == '^') {
                pos++;
                sinpow = readInt();
            } else {
                sinpow = 1;
            }
            // Now expect 'x'
            if (pos < len && str[pos] == 'x') {
                pos++;
            }
        } else if (pos + 3 <= len && str[pos] == 'c' && str[pos+1] == 'o' &&
                   str[pos+2] == 's') {
            pos += 3;
            if (pos < len && str[pos] == '^') {
                pos++;
                cospow = readInt();
            } else {
                cospow = 1;
            }
            // Now expect 'x'
            if (pos < len && str[pos] == 'x') {
                pos++;
            }
        } else {
            break;
        }
    }

    return term(coef, xpow, sinpow, cospow);
}

frac parseFactor() {
    if (pos < len && str[pos] == '(') {
        pos++;
        frac result = parseExpr();
        pos++; // skip ')'
        return result;
    } else if (pos < len && str[pos] == '-') {
        pos++;
        if (pos < len && str[pos] == '(') {
            pos++;
            frac result = parseExpr();
            pos++; // skip ')'
            frac zero(0);
            return zero - result;
        } else {
            term t = parseSingleTerm();
            t.a = -t.a;
            return frac(t);
        }
    } else {
        term t = parseSingleTerm();
        return frac(t);
    }
}

frac parseTerm() {
    frac result = parseFactor();

    while (pos < len && (str[pos] == '*' || str[pos] == '/')) {
        char op = str[pos];
        pos++;
        frac right = parseFactor();

        if (op == '*') {
            result = result * right;
        } else {
            result = result / right;
        }
    }

    return result;
}

frac parseExpr() {
    frac result = parseTerm();

    while (pos < len && (str[pos] == '+' || str[pos] == '-')) {
        char op = str[pos];
        pos++;
        frac right = parseTerm();

        if (op == '+') {
            result = result + right;
        } else {
            result = result - right;
        }
    }

    return result;
}

void solve(char *s, int n) {
    str = s;
    len = n;
    pos = 0;

    frac result = parseExpr();

    result.output();
    cout << endl;

    frac deriv = result.derivate();
    deriv.output();
    cout << endl;
}

int main() {
    string input;
    cin >> input;
    int n = input.length();
    char *s = new char[n + 2]{0};
    for (int i = 0; i < n; ++i) s[i] = input[i];
    solve(s, n);
    delete []s;
    return 0;
}
