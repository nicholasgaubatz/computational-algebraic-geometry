                                                                                                                                                                                                                           2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y y y   + y y y   - y y  y   - y y  y  , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              6 7    6 12    7 12   5 7    5 11    7 11   3 4    3 12    4 12   2 4    2 11    4 11   1 4    1 7    4 7   1 3    1 6    3 6   1 2    1 5    2 5   8 9 10    8 9 12    8 10 12    9 10 12   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2    2   2   2               2   2   2                     2         2         2
          AOTinIdeal => ideal (y  , y  , y  , y , y , y , y y , y y , y , y , y , y y , y y , y y , y , y y , y , y y , y , y y y  , y y y  , y y y  , y y y )
                                12   11   10   9   8   7   6 7   5 7   6   5   4   3 4   2 4   1 4   3   1 3   2   1 2   1   5 6 11   2 3 11   8 9 10   2 3 5
          graph => {set {0, 2}, set {2, 4}, set {2, 5}, set {2, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 3}, set {3, 6}, set {1, 5}, set {4, 6}, set {5, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 59T  + 153T  + 222T  + 171T  + 54T
          hyperplanes => {a - c, c - e, c - f, c - g, a - e, a - f, a - g, b - d, d - g, b - f, e - g, f - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6*y_7-y_6*y_12+y_7*y_12, y_5*y_7-y_5*y_11+y_7*y_11, y_3*y_4-y_3*y_12+y_4*y_12, y_2*y_4-y_2*y_11+y_4*y_11, y_1*y_4-y_1*y_7-y_4*y_7, y_1*y_3-y_1*y_6-y_3*y_6, y_1*y_2-y_1*y_5-y_2*y_5, y_8*y_9*y_10+y_8*y_9*y_12-y_8*y_10*y_12-y_9*y_10*y_12, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}},{{y_12^2, y_11^2, y_10^2, y_9^2, y_8^2, y_7^2, y_6*y_7, y_5*y_7, y_6^2, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_1*y_4, y_3^2, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_5*y_6*y_11, y_2*y_3*y_11, y_8*y_9*y_10, y_2*y_3*y_5}})
G = graph {set {0, 2}, set {2, 4}, set {2, 5}, set {2, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 3}, set {3, 6}, set {1, 5}, set {4, 6}, set {5, 6}}
