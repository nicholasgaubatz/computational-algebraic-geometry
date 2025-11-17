                                                                                                                                                                                             2   2   2   2   2   2   2   2   2   2    2
HashTable{AOTideal => ideal (y y   - y y   - y  y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y y  + y y y   - y y y   - y y y  , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  )}
                              9 10    9 11    10 11   5 6    5 10    6 10   3 4    3 8    4 8   1 4    1 6    4 6   2 4 7    2 4 10    2 7 10    4 7 10   1 2 5    1 2 7    1 5 7    2 5 7   1   2   3   4   5   6   7   8   9   10   11
                                2    2           2   2   2   2         2   2               2   2   2
          AOTinIdeal => ideal (y  , y  , y y  , y , y , y , y , y y , y , y , y y , y y , y , y , y , y y y , y y y , y y y , y y y y , y y y y , y y y y )
                                11   10   9 10   9   8   7   6   5 6   5   4   3 4   1 4   3   2   1   2 4 7   1 3 6   1 2 5   2 3 7 8   1 3 5 8   1 2 6 7
          graph => {set {0, 4}, set {1, 4}, set {2, 4}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 5}, set {2, 6}, set {3, 5}, set {5, 6}, set {3, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 11T + 51T  + 127T  + 178T  + 132T  + 40T
          hyperplanes => {a - e, b - e, c - e, e - g, a - f, a - g, b - f, c - g, d - f, f - g, d - g}
          numVariables => 11
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_11]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_9*y_10-y_9*y_11-y_10*y_11, y_5*y_6-y_5*y_10+y_6*y_10, y_3*y_4-y_3*y_8-y_4*y_8, y_1*y_4-y_1*y_6-y_4*y_6, y_2*y_4*y_7+y_2*y_4*y_10-y_2*y_7*y_10-y_4*y_7*y_10, y_1*y_2*y_5-y_1*y_2*y_7-y_1*y_5*y_7+y_2*y_5*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}},{{y_11^2, y_10^2, y_9*y_10, y_9^2, y_8^2, y_7^2, y_6^2, y_5*y_6, y_5^2, y_4^2, y_3*y_4, y_1*y_4, y_3^2, y_2^2, y_1^2, y_2*y_4*y_7, y_1*y_3*y_6, y_1*y_2*y_5, y_2*y_3*y_7*y_8, y_1*y_3*y_5*y_8, y_1*y_2*y_6*y_7}})
G = graph {set {0, 4}, set {1, 4}, set {2, 4}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 5}, set {2, 6}, set {3, 5}, set {5, 6}, set {3, 6}}
