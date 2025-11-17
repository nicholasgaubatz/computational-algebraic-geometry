                                                                                                                                                                     2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y y  + y y y   - y y y   - y y y  , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  )}
                              5 6    5 10    6 10   3 4    3 8    4 8   1 4    1 6    4 6   2 4 7    2 4 10    2 7 10    4 7 10   1 2 5    1 2 7    1 5 7    2 5 7   1   2   3   4   5   6   7   8   9   10
                                2    2   2   2   2         2   2               2   2   2
          AOTinIdeal => ideal (y  , y , y , y , y , y y , y , y , y y , y y , y , y , y , y y y , y y y , y y y , y y y y , y y y y , y y y y )
                                10   9   8   7   6   5 6   5   4   3 4   1 4   3   2   1   2 4 7   1 3 6   1 2 5   2 3 7 8   1 3 5 8   1 2 6 7
          graph => {set {0, 4}, set {1, 4}, set {2, 4}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 5}, set {2, 6}, set {3, 5}, set {5, 6}}
                                  2      3       4      5      6
          hSeries => 1 + 10T + 42T  + 94T  + 117T  + 76T  + 20T
          hyperplanes => {a - e, b - e, c - e, e - g, a - f, a - g, b - f, c - g, d - f, f - g}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_5*y_6-y_5*y_10+y_6*y_10, y_3*y_4-y_3*y_8-y_4*y_8, y_1*y_4-y_1*y_6-y_4*y_6, y_2*y_4*y_7+y_2*y_4*y_10-y_2*y_7*y_10-y_4*y_7*y_10, y_1*y_2*y_5-y_1*y_2*y_7-y_1*y_5*y_7+y_2*y_5*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}},{{y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_5*y_6, y_5^2, y_4^2, y_3*y_4, y_1*y_4, y_3^2, y_2^2, y_1^2, y_2*y_4*y_7, y_1*y_3*y_6, y_1*y_2*y_5, y_2*y_3*y_7*y_8, y_1*y_3*y_5*y_8, y_1*y_2*y_6*y_7}})
G = graph {set {0, 4}, set {1, 4}, set {2, 4}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 5}, set {2, 6}, set {3, 5}, set {5, 6}}
