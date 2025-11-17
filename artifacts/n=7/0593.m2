                                                                                                                                                                                                        2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y y y  - y y y y  + y y y y  - y y y y  - y y y y , y y y y  - y y y y  + y y y y  - y y y y  - y y y y , y , y , y , y , y , y , y , y , y , y  )}
                              5 7    5 10    7 10   4 7    4 9    7 9   4 6    4 8    6 8   1 2 3 8    1 2 3 9    1 2 8 9    1 3 8 9    2 3 8 9   1 2 3 6    1 2 3 7    1 2 6 7    1 3 6 7    2 3 6 7   1   2   3   4   5   6   7   8   9   10
                                2    2   2   2               2         2   2   2   2   2
          AOTinIdeal => ideal (y  , y , y , y , y y , y y , y , y y , y , y , y , y , y , y y y , y y y , y y y y , y y y y , y y y y )
                                10   9   8   7   5 7   4 7   6   4 6   5   4   3   2   1   4 5 9   6 7 8   5 6 8 9   1 2 3 8   1 2 3 6
          graph => {set {0, 3}, set {3, 6}, set {0, 5}, set {1, 4}, set {2, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 6}}
                                  2      3       4      5      6
          hSeries => 1 + 10T + 42T  + 96T  + 127T  + 92T  + 28T
          hyperplanes => {a - d, d - g, a - f, b - e, c - e, e - f, e - g, b - f, b - g, c - g}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-4}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_5*y_7-y_5*y_10-y_7*y_10, y_4*y_7-y_4*y_9-y_7*y_9, y_4*y_6-y_4*y_8-y_6*y_8, y_1*y_2*y_3*y_8-y_1*y_2*y_3*y_9+y_1*y_2*y_8*y_9-y_1*y_3*y_8*y_9-y_2*y_3*y_8*y_9, y_1*y_2*y_3*y_6-y_1*y_2*y_3*y_7+y_1*y_2*y_6*y_7-y_1*y_3*y_6*y_7-y_2*y_3*y_6*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}, {-4}, {-4}},{{y_10^2, y_9^2, y_8^2, y_7^2, y_5*y_7, y_4*y_7, y_6^2, y_4*y_6, y_5^2, y_4^2, y_3^2, y_2^2, y_1^2, y_4*y_5*y_9, y_6*y_7*y_8, y_5*y_6*y_8*y_9, y_1*y_2*y_3*y_8, y_1*y_2*y_3*y_6}})
G = graph {set {0, 3}, set {3, 6}, set {0, 5}, set {1, 4}, set {2, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 6}}
