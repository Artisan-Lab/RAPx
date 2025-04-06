#!/bin/bash
#该脚本在目录下为每个Cargo项目执行相同的命令直到报错

# All arguments passed to this script are forwarded to cargo rapx
# Example: batch.sh -F -M

# 解析脚本传入的参数
function parse() {
  F=0 #uaf
  M=0 #mleak
  O=0 #opt
  rest="" #other args
  for arg in "$@"; do
    case "$arg" in
    -F) F=1 ;;
    -M) M=1 ;;
    -O) O=1 ;;
    *) rest="$rest $arg" ;;
    esac
  done
}

# 查找并编译给定目录下的所有 Rust 项目
function test() { #第一个参数：目录名 第二个参数：rapx的参数
  cur=$(pwd)
  target_dir=$1
  args=$2

  find $target_dir -type f -name "Cargo.toml" | while read -r cargo_file; do
    # 获取 Cargo.toml 文件所在的目录
    project_dir=$(dirname "$cargo_file")

    echo "Processing project in: $project_dir"

    # 切换到项目目录
    pushd "$project_dir" >/dev/null

    if [ $# -eq 1 ]; then #检查函数是否只有target_dir这一个参数
      cmd="cargo clean"
      echo "No analysis argument is specified: run \`$cmd\` in $project_dir"
      $cmd
      # 返回原始目录
      popd >/dev/null
      continue
    else
      cmd="cargo rapx $args"
      $cmd 2>&1 | tee $cur/rapx.txt | ansi2txt | grep 'RAP|WARN|' && echo -e "\033[32m$project_dir pass\033[0m"
    fi

    if [ $? -ne 0 ]; then
      echo -e "\033[31mError: '$cmd' doesn't emit WARN diagnostics in $project_dir \033[0m\nRAP output:"
      cat $cur/rapx.txt
      exit 1
    fi

    cat $cur/rapx.txt | ansi2txt | grep 'RAP|ERROR|'
    if [ $? -eq 0 ]; then
      echo -e "Error: '$cmd' contains error message in $project_dir \nRAP output:"
      cat $cur/rapx.txt
      exit 1
    fi

    # 返回原始目录
    popd >/dev/null
  done
}

parse $@
if [ "$F" -eq 1 ]; then
  test "support/uaf" "-F $rest"
fi
if [ "$M" -eq 1 ]; then
  test "support/leak" "-M $rest"
fi
if [ "$O" -eq 1 ]; then
  test "support/opt" "-O $rest"
fi
if [ $(($F + $M + $O)) -eq 0 ]; then
  test "support" $rest
fi
