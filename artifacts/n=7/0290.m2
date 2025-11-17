                                                                                                                                                                                                     2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y   - y y   - y  y  , y y   - y y   - y  y  , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              9 10    9 12    10 12   8 10    8 11    10 11   6 7    6 10    7 10   4 5    4 10    5 10   2 3    2 7    3 7   1 3    1 5    3 5   1 2 4    1 2 6    1 4 6    2 4 6   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2                  2   2   2         2   2         2   2               2   2
          AOTinIdeal => ideal (y  , y  , y  , y y  , y y  , y , y , y , y y , y , y , y y , y , y , y y , y y , y , y , y y y  , y y y , y y y )
                                12   11   10   9 10   8 10   9   8   7   6 7   6   5   4 5   4   3   2 3   1 3   2   1   8 9 11   1 2 5   1 2 4
          graph => {set {0, 4}, set {1, 4}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {3, 5}, set {5, 6}, set {2, 6}, set {3, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 60T  + 159T  + 234T  + 180T  + 56T
          hyperplanes => {a - e, b - e, e - g, a - f, a - g, b - f, b - g, c - f, d - f, f - g, c - g, d - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_9*y_10-y_9*y_12-y_10*y_12, y_8*y_10-y_8*y_11-y_10*y_11, y_6*y_7-y_6*y_10+y_7*y_10, y_4*y_5-y_4*y_10+y_5*y_10, y_2*y_3-y_2*y_7-y_3*y_7, y_1*y_3-y_1*y_5-y_3*y_5, y_1*y_2*y_4-y_1*y_2*y_6-y_1*y_4*y_6+y_2*y_4*y_6, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}},{{y_12^2, y_11^2, y_10^2, y_9*y_10, y_8*y_10, y_9^2, y_8^2, y_7^2, y_6*y_7, y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1^2, y_8*y_9*y_11, y_1*y_2*y_5, y_1*y_2*y_4}})
G = graph {set {0, 4}, set {1, 4}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {3, 5}, set {5, 6}, set {2, 6}, set {3, 6}}
