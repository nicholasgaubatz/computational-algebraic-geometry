                                                                                     2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y )}
                              1 2    1 3    2 3   4 5 6    4 5 7    4 6 7    5 6 7   1   2   3   4   5   6   7
                                2   2   2   2   2   2         2
          AOTinIdeal => ideal (y , y , y , y , y , y , y y , y , y y y )
                                7   6   5   4   3   2   1 2   1   4 5 6
          graph => {set {0, 3}, set {3, 4}, set {0, 4}, set {1, 5}, set {2, 5}, set {1, 6}, set {2, 6}}
                                 2      3      4     5
          hSeries => 1 + 7T + 20T  + 29T  + 21T  + 6T
          hyperplanes => {a - d, d - e, a - e, b - f, c - f, b - g, c - g}
          numVariables => 7
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_7]
AOTideal = ideal map(R^1,R^{{-2}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_2-y_1*y_3-y_2*y_3, y_4*y_5*y_6-y_4*y_5*y_7-y_4*y_6*y_7+y_5*y_6*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}},{{y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1*y_2, y_1^2, y_4*y_5*y_6}})
G = graph {set {0, 3}, set {3, 4}, set {0, 4}, set {1, 5}, set {2, 5}, set {1, 6}, set {2, 6}}
