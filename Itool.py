# -*- coding: utf-8 -*-
# from __future__ import unicode_literals#为了解决该问题
# ，这样python2中字符的行为将和python3中保持一致，python2中定义普通字符将自动识别为unicode

from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.mime.image import MIMEImage
from simhash import Simhash
import smtplib
import requests
import threading
import time
import regex as re
import random
import hashlib
import base64
import traceback
import json
import sys
import os
import inspect
import ctypes
import socket
import uuid
import logging
import urllib.parse
import html.parser as HTML_PARSER
from posixpath import normpath
import copy
import six
import imp
try:
    from StringIO import StringIO as stringio  # python2
except BaseException:
    from io import BytesIO as stringio  # pythpn 3
import gzip

if sys.version[0] == '2':
    imp.reload(sys)
    sys.setdefaultencoding("utf-8")
    from urllib.parse import urlparse, urlunparse, urljoin
else:
    from urllib.parse import urlparse, urlunparse, urljoin
from datetime import datetime
reg_escape = re.compile(r'(\^|\$|\(|\)|\*|\+|\?|\.|\[|\]|\\|\{|(?:\|))'
                        )  # 首先进行转义存在标签参数的 暂时不转义  后面会进行替换
reg_sub_to_py = re.compile(r'\$(\d+)')  # c#中替换字符组用$ 而python用\
RE_CHAR = re.compile(r'[\r\t]')  # 检测字符中是否存在换行标签 防止字符提取不到进行替换
# 正则自动提取网址
RE_REPLACE_TABLE = re.compile(r'''^[^<]+[^\u4e00-\u9fa5]>|<[^\u4e00-\u9fa5][^>]+$|^>|<$''')  # 替换不闭合标签

RE_DISPLAY_NONE = re.compile(r'''<(\s*[\w]+)[^>]*?display:\s*none["']>''', re.I)  # 检测隐藏标签

RE_SPECIAL_CHAR = re.compile(r'''[^u4e00-u9fa5\w"'\s/&:|*!@#$%^&*(),?{}\[\]+_=-]''')  # 匹配是否存在特殊字符

re_relative_url = re.compile(r'''(?:(?:href|src)(?:&quot;|\s)?=(?:&quot;|\s)?(["'])([\s\S]{5,1000}?)\1)|(?:(?:href|src)(?:&quot;|\s)?=(?:&quot;|\s)?([\s\S]{5,1000}?)(?:&quot;| ))''', flags=re.I)
# 正则自动提取base 标签网址  用来自动拼接网址
re_base_url = re.compile(r'''(?:base(?:&quot;|\s){1,3}href(?:&quot;|\s)?=(?:&quot;|\s)?(["'])([\s\S]{5,1000}?)\1)|(?:base(?:&quot;|\s){1,3}href(?:&quot;|\s)?=(?:&quot;|\s)?([\s\S]{5,1000}?)(?:&quot;| ))''', flags=re.I)
class ThreadEX(threading.Thread):
    '''继承多线程类   增加get_args命令 用来获取传入的参数 当网页被封的时候用来回收传入的参数'''

    class CustomTask(object):
        '''在threading中传入的函数中 没有返回值   自己定义一个类  用来接收返回的值  然后传入到多线程中就能获取返回值了 '''

        def __init__(self, target):
            self._result = None
            self.__target = target

        def run(self, *args, **kwargs):
            # 你的代码, 你用来进行多线程
            result = None
            try:
                if self.__target:
                    result = self.__target(*args, **kwargs)
            finally:
                # Avoid a refcycle if the thread is running a function with
                # an argument that has a member that points to the thread.
                del self.__target
            self._result = result

        def get_result(self):
            return self._result

    def __init__(self,
                 group=None,
                 target=None,
                 name=None,
                 args=(),
                 kwargs=None,
                 verbose=None):
        # 定义一个类初始化的时候接受一个函数  调用get_result 返回 返回值
        func = self.CustomTask(target)
        threading.Thread.__init__(self, group, func.run, name, args, kwargs,
                                  verbose)
        # 注意要显示调用父类构造方法，并传递参数self
        self.__func = func
        self.__my_args = args
        # 线程标记在线程的各个阶段通过threading.current_thread() 获取线程对象
        # 然后set_thread_status设置该值   get_thread_status 获取该值  防止线程卡死
        self.__thread_status = None

    def get_args(self):
        return self.__my_args

    def get_thread_status(self):
        return self.__thread_status

    def set_thread_status(self, status):
        self.__thread_status = status

    def get_result(self):
        '''获取函数的返回值   必须在函数执行完成后获取否则返回  None'''
        return self.__func.get_result()


class LockEX:
    '''自己定义的锁  增加了设置等待执行的命令 set_wait_status
        该命令的作用是当我们要强制结束一条线程  如果该线程正处于锁定状态
        我们要在结束线程之前调用 把 get_wait_status 设置为True  再调用Lock_All_release()
         当我们解锁的时候 防止线程继续执行添加了1秒的等待  从而达到了强制结束线程导致的卡死'''

    def __init__(self):
        self.lock = threading.Lock()
        self.status_lock = threading.Lock()
        self.wait = False  # 延迟解锁   在强制结束线程的时候  必须先对所有的锁解除  但是解除后希望不执行后面的语句  就被干掉
        # 所以在解锁后下一个语句执行延迟1秒来达到强杀的目的
        self.lock_num = 0
        self.__status = False  # 用来标记状态 默认 false  或 True 两种情况  跟锁的功能独立开来  只是增加的一个功能

    def acquire(self):
        self.status_lock.acquire()
        self.lock_num += 1  # 用来获取当前被执行的次数
        self.status_lock.release()
        self.lock.acquire()
        if self.wait:
            Time_Sleep(1)

    def release(self):
        self.lock.release()
        self.status_lock.acquire()
        self.lock_num -= 1  # 用来获取当前被执行的次数
        self.status_lock.release()

    def get_wait_status(self):
        return self.wait

    def set_wait_status(self, status):
        self.wait = status

    def get_lock_num(self):
        '''获取当前锁的数量'''
        self.status_lock.acquire()
        num = self.lock_num
        self.status_lock.release()
        return num

    def get_status(self):
        '''获取状态   用来控制某一个流程只有一个线程执行的判断'''
        self.status_lock.acquire()
        status = self.__status
        self.status_lock.release()
        return status

    def set_status(self, status):
        '''设置状态   用来控制某一个流程只有一个县线程执行的判断'''
        self.status_lock.acquire()
        self.__status = status
        self.status_lock.release()

    def set_status_EX(self, status):
        '''设置状态  设置状态之前先判断原来的状态 如果跟原来的状态一直就返回True  否则返回False'''
        self.status_lock.acquire()
        if self.__status == status:
            ret_status = True
        else:
            self.__status = status
            ret_status = False
        self.status_lock.release()
        return ret_status


# 封装的日志输出类
class Log:
    '''对logging进行高级的封装 封装一些方法'''

    fh_level = None  # 记录文本日志的输出级别
    ch_level = None  # 记录cmd日志的输出级别
    logger = logging.getLogger()
    logger.setLevel(logging.ERROR)
    # 建立一个filehandler来把日志记录在文件里，级别为debug以上
    fh = logging.FileHandler("run.log")
    fh.setLevel(logging.INFO)
    # 建立一个streamhandler来把日志打在CMD窗口上，级别为error以上
    ch = logging.StreamHandler()
    ch.setLevel(logging.ERROR)
    # 设置日志格式
    formatter = logging.Formatter("%(asctime)s - %(levelname)s - %(message)s")
    ch.setFormatter(formatter)
    fh.setFormatter(formatter)
    # 将相应的handler添加在logger对象中
    logger.addHandler(ch)
    logger.addHandler(fh)

    def log(self, msg=None, level=logging.INFO, *args, **kwargs):
        '''默认输出的级别为info  如果多任务的时候 可以设置cmd窗口输出的等级为error以上'''
        self.logger.log(level, msg=msg, *args, **kwargs)

    def set_fh_level(self, level):
        '''设置输出文本 的输出级别'''
        self.fh.setLevel(level)
        self.fh_level = level

    def set_ch_level(self, level):
        '''设置cmd输出 的输出级别'''
        self.ch.setLevel(level)
        self.ch_level = level

    def set_log_name(self, name):
        '''设置输出文件的名字   要带上log后缀
            默认日志后缀为 run.log'''
        fh = logging.FileHandler(name)  # 设置日志名字
        if self.fh_level is None:
            fh.setLevel(logging.INFO)  # 设置输出等级
        else:
            fh.setLevel(self.fh_level)
        fh.setFormatter(self.formatter)  # 设置输出格式
        self.logger.addHandler(fh)  # 添加到打印队列
        self.logger.removeHandler(self.fh)  # 删除原来文本的 hander对象


# Lg = Log()#初始化logging模块
# 没有完成 暂时屏蔽
def log(msg, level=logging.INFO, *args, **kwargs):
    '''默认输出的日志级别的INFO
        level的级别的调用logging中的级别
        例如 logging.DEBUG
        输入参数跟logging.log一致'''
    Lg.log(msg=msg, level=level, *args, **kwargs)


# 传入adsl名字  账号 密码 进行ip更换   适合动态vps更换ip
def ADSL_reconnect(name, user, pwd):
    for nn in range(4):
        os.popen("rasdial {} /DISCONNECT".format(name))
        Time_Sleep(2)  # 调用自己定义的延迟 防止多线程结束的时候卡死
        ret = os.popen("rasdial ")
        text = ret.read()
        if '没有连接' in text.decode('gbk'):
            print(('{}    已成功断开连接'.format(get_time_str())))
            break
        else:
            if nn < 4:
                print(('{}  断开失败 再来一次'.format(get_time_str())))
            Time_Sleep(3)
    for nn in range(4):
        ret = os.popen("rasdial {} {} {}".format(name, user, pwd))
        text = ret.read()
        if '已连接' in text.decode('gbk'):
            print(('{}  已经成功拨号'.format(get_time_str())))
            return 1, None  # 返回1表示成功拨号
            break
        elif '电话占线' in text.decode('gbk'):
            print((text.decode('gbk')))
            return -1, text.decode('gbk')  # 通知调用的函数发生错误   并返回错误信息
        else:
            if nn < 4:
                print(('{}  拨号失败 再来一次'.format(get_time_str())))
            Time_Sleep(3)
    return -1, text.decode('gbk')  # 通知调用的函数发生错误   并返回错误信息


# threading中解锁阻塞的lock  必须用LockEX 自定义的类进行定义锁  不懂底层原理慎用
def Lock_All_release(lock):
    '''传入一个锁 把这个锁完全解除  就是多次调用 lock.release
       可以在 stop_thread 函数执行前使用  调用用来解除阻塞的线程
       防止再次调用的时候线程卡死  这个锁必须使用的是自己定义的LockEX类'''
    lock.set_wait_status(True)
    while True:
        try:
            lock.release()
            # print '解锁'
        except Exception as e:
            # print e
            break
    lock.set_wait_status(False)


# 程序延迟  threadingz中使用  精度没有time.sleep准确  但是可以防止强制结束现成的时候导致程序卡死
def Time_Sleep(Interval):
    '''传入一个时间 让脚本等待   若果是多线程的话 不能使用系统内部的time.sleep
        如果使用这个命令的话  调用stop_thread 命令就会失效   无法强制结束一个线程 '''
    t = time.clock()
    time_num = 0  # 如果获取的当前时间 time.clock() - t存在负数  就马上会造成卡死
    # 把t重新赋值   这样不支持精确的延迟 默认忽略了代码的执行时间
    while True:
        t1 = time.clock() - t
        if t1 > Interval:
            break
        elif t1 < 0:
            t = time.clock()
            time_num += 1

        if time_num >= Interval * 1000 and time_num > 0:
            print(('时间差存在负数  出现次数{}'.format(time_num)))
            break

        time.sleep(0.001)


# 强制向线程中注入异常让线程退出
def _async_raise(tid, exctype):
    """raises the exception, performs cleanup if needed"""
    tid = ctypes.c_long(tid)
    if not inspect.isclass(exctype):
        exctype = type(exctype)
    res = ctypes.pythonapi.PyThreadState_SetAsyncExc(tid,
                                                     ctypes.py_object(exctype))
    if res == 0:
        raise ValueError("invalid thread id")
    elif res != 1:
        # """if it returns a number greater than one, you're in trouble,
        # and you should call it again with exc=NULL to revert the effect"""
        ctypes.pythonapi.PyThreadState_SetAsyncExc(tid, None)
        raise SystemError("PyThreadState_SetAsyncExc failed")


# 强制结束一条线程  目前不稳定
def stop_thread(thread):
    '''传入一个线程对象  通过向线程中注入SystemExit 强制退出线程
        目前发现的问题  如果当前线程被锁  或者在线程中运行了time.sleep 会导致无法强制结束线程
        这两个问题目前的解决方法  如果线程中要加锁 就用自己定义的LockEX类 这个可以设置解锁的时候等待1秒后执行 从而可以达到强制结束目的
        如果要在线程中使用time.sleep延迟的话  用自己写的函数 Time_Sleep()  可以解决卡死的问题
        其他问题不详 待测试'''
    _async_raise(thread.ident, SystemExit)


# 获取本机的mac
def get_mac_address():
    '''获取本机的mac地址'''
    mac = uuid.UUID(int=uuid.getnode()).hex[-12:]
    return ":".join([mac[e:e + 2] for e in range(0, 11, 2)])


# 获取当前的内网ip
def get_localIP():
    '''获取电脑的内网ip地址'''
    localIP = socket.gethostbyname(
        socket.gethostname())  # gethostname 获取主机名，gethostbyname转换主机名为IP
    #print ("本机本地IP是：%s\n\n" % localIP)
    return localIP


# 通过访问ip138 获取当前网络的外网ip
def get_ip():
    '''获取外网的ip  返回ip  和 归属地  vpn可以过滤速度慢的ip'''
    for x in range(2):
        content = ''
        try:
            r = requests.get('http://1212.ip138.com/ic.asp', timeout=5)
            r.encoding = 'gbk'
            content = r.text
            break
        except BaseException:
            pass
    if content == '':
        return None, None  # 表示获取ip失败
    # print content
    ip = ''.join(
        re.findall(r'\[(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})\]', content))

    local = ''.join(re.findall(r'来自：(.{1,20}?)</center>', content))

    return ip, local


# 强制结束指定名字的线程
def Forced_close_thread(thread_obj, args=None, name='run_main'):
    '''thread_obj    传入import的threading对象
    强制结束正在运行的线程 同时回收所有线程的参数  回收的参数会添加到args列表中  如果args=None 就不回收参数'''
    active_thread_list = thread_obj.enumerate()  # 获取正在运行的线程
    for thread in active_thread_list:
        thread_name = thread.getName()
        if name in thread_name:  # 检测运行中的线程中是否存在运行的线程
            # print '即将回收的参数',thread.get_args()
            try:
                if args is not None:
                    args.append(thread.get_args()[0])  # 回收强制结束线程的参数
                stop_thread(thread)
            except Exception as err:
                print(err)


# 传入线程对象 等待指定线程名的线程结束
def wait_thread(thread_obj, num=None, name='run_main', timeout=600):
    '''thread_obj 传入threading对象
    等待线程  判断是否已经达到指定的线程数量否则就一直等待下去 默认等待所有线程结束
     name为要等待结束的线程名字  在启动的时候自己定义 如果不定义默认thread-
    如果传入指定数量  表示只要主线运行线程小于指定数量就返回  默认超时10分钟  成功返回true  超时返回false'''
    if num is None:
        Thread_num = 0
    else:
        Thread_num = num - 1
    tt = time.clock()  # 用来判断等待是否超时
    while True:  # 等待所有线程结束 或者小于指定数量
        if time.clock() - tt >= timeout:
            # 超时直接返回
            return False
        active_count = thread_active_num(thread_obj, name)
        if active_count <= Thread_num:
            break
        else:
            time.sleep(0.1)
    return True


# 获取指定线程名 当前运行的线程数量      可以用来控制线程数  例如爬取10条线程进行网页爬取  通过调用本函数来判断启动的线程数量
def thread_active_num(thread_obj, name):
    '''thread_obj 传入threading对象
    传入线程名字返回 该名字正在运行的线程数量
    例如差un如name为run_main 就返回当前所有正在运行的 线程名为run_main 的线程
        '''
    active_thread_list = thread_obj.enumerate()  # 获取正在运行的线程
    active_count = 0
    for thread in active_thread_list:
        thread_name = thread.getName()
        if name in thread_name:  # 检测运行中的线程中是否存在运行的线程
            active_count += 1
    return active_count


# 回收线程参数  当一个线程检测到异常  在退出之前把原来传入的参数回收到list中     例如 爬虫检测到ip异常
# 此时传入的url理论上会爬取失败 这个时候需要把传入的参数进行回收后 下次继续使用
def Recovery_account(thread_obj, args=None):
    '''存入多线程对象   回收线程名为 run_main 的子线程的参数'''
    if args is None:
        return 0
    active_thread_list = thread_obj.enumerate()  # 获取正在运行的线程
    for thread in active_thread_list:
        thread_name = thread.getName()
        if 'run_main' in thread_name:  # 检测运行中的线程中是否存在运行的线程
            # print '待回收的值',thread.get_args()
            args.append(thread.get_args()[0])  # 回收线程的参数



# 网页gzip 压缩 解压
def gzip_compress(content):
    """
    :param content: 传入byte类型的字符进行gzip 压缩
    :return:  返回压缩后的字节
    """
    buf = stringio()
    with gzip.GzipFile(mode="wb", compresslevel=9, fileobj=buf) as g:
        g.write(content)
    buf_data = buf.getvalue()
    buf.close()
    if not buf_data:
        return content
    return buf_data

def gzip_decompress(content):
    """
    :param content: 传入byte类型的字符进行gzip 解压
    :return:  返回压缩后的字节
    """
    buf = stringio(content)
    with gzip.GzipFile(mode="rb", compresslevel=9, fileobj=buf) as g:
        buf_data = g.read()
    if not buf_data:
        return content
    return buf_data


# 发送邮件
def send_mail(mail_list,
              mail_title,
              mail_msg,
              mail_type='plain',
              mail_charset='utf-8',
              filename=''):
    # 创建一个带附件的实例
    msg = MIMEMultipart()

    # 正文内容
    txt = MIMEText(mail_msg, mail_type, mail_charset)
    msg.attach(txt)

    # 构造附件
    if filename:
        att = MIMEText(open(filename, 'rb').read(), 'base64', 'utf-8')
        att["Content-Type"] = 'application/octet-stream'
        att["Content-Disposition"] = 'attachment; filename="' + filename + '"'
        msg.attach(att)

    msg['from'] = 'contact@zhongbiao.mobi'
    msg['subject'] = mail_title + 'err_IP ' + socket.gethostbyname(
        socket.gethostname())
    # 邮件发送
    msg['to'] = mail_list
    to_mail = mail_list.split(',')
    # 邮件抄送
    # msg['cc'] = cc_list
    # 邮件密送
    # msg['bcc'] = bcc_list

    # 发送邮件
    server = smtplib.SMTP()
    server.connect('smtp.qiye.163.com')
    server.login('contact@zhongbiao.mobi', '4rfvBHU*59')
    server.sendmail(msg['from'], to_mail, msg.as_string())
    server.quit()



def send_mail_all(mail_list, mail_title, mail_msg, mail_type='plain', mail_charset='utf-8', filelist=[], imagelist=[]):
    """支持发送图片 附件"""
    # 创建一个带附件的实例
    msg = MIMEMultipart()

    # 正文内容
    txt = MIMEText(mail_msg, mail_type, mail_charset)
    msg.attach(txt)

    # 构造图片信息
    if imagelist:
        for data in imagelist:
            if isinstance(data, str):
                row_data = open(data, 'rb').read()

            else:
                row_data = data


            image = MIMEImage(row_data)
            image.add_header('Content-ID', '<image1>')
            msg.attach(image)


    # 构造附件
    if filelist:
        for data in filelist:
            if isinstance(data, str):
                row_data = open(data, 'rb').read()
                filename = data
            else:
                row_data = data
                filename = str_to_md5(data)
            att = MIMEText(row_data, 'base64', 'utf-8')
            att["Content-Type"] = 'application/octet-stream'
            att["Content-Disposition"] = 'attachment; filename="' + filename + '"'
            msg.attach(att)

    msg['from'] = 'contact@zhongbiao.mobi'
    msg['subject'] = mail_title
    # 邮件发送
    msg['to'] = mail_list
    to_mail = mail_list.split(',')
    # 邮件抄送
    # msg['cc'] = cc_list
    # 邮件密送
    # msg['bcc'] = bcc_list

    # 发送邮件
    server = smtplib.SMTP()
    server.connect('smtp.qiye.163.com')
    server.login('contact@zhongbiao.mobi', '4rfvBHU*59')
    server.sendmail(msg['from'], to_mail, msg.as_string())
    server.quit()

# is_reverse 为1时，用于其他提取函数的入参，因为提取函数处理的内容中括号全部是英文括号
def transfer_org_name(in_org_name, is_reverse="0"):
    if in_org_name:
        if is_reverse == "1":
            org_name = in_org_name.replace('（', '(').replace('）', ')')
        else:
            org_name = in_org_name.replace('(', '（').replace(')', '）')
    else:
        org_name = None
    return org_name


# 把中文括号转换成英文括号
def transfer_content(in_content):
    out_content = in_content.replace(
        '（',
        '(').replace(
        '）',
        ')').replace(
            '﹙',
            '(').replace(
                '﹚',
                ')'). replace(
                    '：',
                    ':').replace(
                        r'〔',
                        r'(').replace(
                            r'〕',
                            r')').replace(
                                '．',
                                '.').replace(
                                    '，',
        ',')
    return out_content


# 机构id生成参数
re_status1 = re.compile('开业|在业|在营|正常|存续|登记|11|经营')  # 表示该企业正常的
re_status2 = re.compile('迁|异地')  # 表示该企业迁出
re_status3 = re.compile('销|停|2|3|14')  # 表示该企业注销
reg_status_mapping = {
    '开业': '',
    '在业': '',
    '在营（开业）': '',
    '在营(开业)': '',
    '在营（开业）企业': '',
    '正常': '',
    '正常在业': '',
    '存续(在营、开业、在册)': '',
    '存续（在营、开业、在册）': '',
    '存续': '',
    '登记成立': '',
    '筹建': '',
    '数据补录中': '',
    '迁出': '',
    '迁移异地': '',
    '其他': '2',
    '个体转企业': '2',
    '撤销': '3',
    '吊销': '3',
    '吊销企业': '3',
    '已吊销': '3',
    '吊销，未注销': '3',
    '吊销,未注销': '3',
    '吊销未注销': '3',
    '已注销': '3',
    '注销': '3',
    '停业': '3',
    '注销企业': '3',
    '清算中': '3',
    '清算': '3'
}


def get_org_id(company_name, reg_state=None):
    if not reg_state:
        reg_status = ''
    else:
        reg_status = reg_status_mapping.get(reg_state, '-1')
        if reg_status == '-1':
            re_text = re_status1.search(reg_state)
            if re_text:
                reg_status = ''

        if reg_status == '-1':
            re_text = re_status3.search(reg_state)
            if re_text:
                reg_status = '3'
        # 最后实在没有找到对应编号 直接赋值为空
        if reg_status == '-1':
            reg_status = ''

    new_org_id = get_org_uuid(company_name + reg_status)
    return new_org_id


# 生成工商信息的uuid
def get_org_uuid(in_org_name):
    if not isinstance(in_org_name, str):
        # 传入字段不是字符串 直接返回
        return ''
    in_org_name = in_org_name.replace('(', '（').replace(')',
                                                        '）').encode('utf8')
    org_uuid1 = hashlib.md5(
        '|'.join(('org_uuid_gen', in_org_name))).hexdigest()
    org_uuid2 = org_uuid1[0: 8] + '-' + org_uuid1[8: 12] + '-' + \
        org_uuid1[12: 16] + '-' + org_uuid1[16: 20] + '-' + org_uuid1[20: 32]
    return org_uuid2


# string封装有一些字符串操作

def check_time(data_str):
    """
    检查传入的时间是否超过当前时间
    :param data_str: 传入时间2017-06-16
    :return: 如果传入时间异常或者 超过当前时间返回False  否则返回True
    """
    try:
        output_time = datetime.strptime(data_str, '%Y-%m-%d')
        now_time = datetime.today()
        if output_time > now_time:
            return False
        else:
            return True
    except Exception as e:
        return False
# 会将17-05-14  自动转换成2017-05-14
# 从文本中提取YYYY-MM-DD格式时间
# default_flag:0默认为空;1默认当前日期
# limit_flag:1大于当前日期时变为当前日期;0不限制
def time_extract_ex(date_str, default_flag=0, limit_flag=0):

    date_str = filter_space_splash(
        date_str.replace("年", '-').replace("月", '-'))
    # 分隔符不严格匹配，不考虑没有分隔符情况，只取2位年
    date_pattern = (
        r'(?:0[048]|[2468][048]|[13579][26])(?:[-./])0?2(?:[-./])29|'
        r'[0-9]{2}(?:[-./])(?:(?:1[02]|0?[13578])(?:[-./])31|'
        r'(?:1[0-2]|0?[13-9])(?:[-./])(?:29|30)|'
        r'(?:1[0-2]|0?[1-9])(?:[-./])(?:2[0-8]|1[0-9]|0?[1-9]))')
    # 备用正则，分隔符匹配，考虑没有分隔符情况，必须4位年,从1900-2999
    date_pattern1 = (
        r'(?:((?:19|2[0-9])(?:0[48]|[2468][048]|[13579][26]))|2[048]00)0?229|'
        r'(?:19|2[0-9])[0-9]{2}(?:(?:1[02]|0?[13578])31|'
        r'(?:1[0-2]|0?[13-9])(?:29|30)|'
        r'(?:1[0-2]|0?[1-9])(?:2[0-8]|1[0-9]|0?[1-9]))')

    date_reg = re.search(date_pattern, date_str)
    try:
        if date_reg:
            # 默认获取当前世纪的信息，年份前2位
            output_time = time.strftime(
                "%Y")[0:2] + date_reg.group(0).replace('.', '-').replace('/', '-')
            output_time = datetime.strptime(
                output_time, '%Y-%m-%d').strftime('%Y-%m-%d')
        # 第一种方式未获取成功
        else:
            date_reg = re.search(date_pattern1, date_str)
            # print date_reg.group(0)
            if date_reg:
                output_time = date_reg.group(0)
                output_time = datetime.strptime(
                    output_time, '%Y%m%d').strftime('%Y-%m-%d')
            else:
                output_time = time.strftime(
                    "%Y-%m-%d") if default_flag else None
    except Exception as e:
        output_time = time.strftime("%Y-%m-%d") if default_flag else None
    return output_time if (not limit_flag or output_time <= time.strftime(
        "%Y-%m-%d")) else time.strftime("%Y-%m-%d")

# 从文本中提取YYYY-MM-DD格式时间   也可以用于时间的转换 例如传入1994.10.20 会自动转换成1994-10-20
def time_extract(date_str):

    date_str = filter_space_splash(
        date_str.replace("年", '-').replace("月", '-'))
    # 分隔符不严格匹配，不考虑没有分隔符情况
    date_pattern = r'(?:19|2[0-9])(?:(?:0[048]|[2468][048]|[13579][26])(?:[-./])0?2(?:[-./])29|[0-9]{2}(?:[-./])(?:(?:1[02]|0?[13578])(?:[-./])31|(?:1[0-2]|0?[13-9])(?:[-./])(?:29|30)|(?:1[0-2]|0?[1-9])(?:[-./])(?:2[0-8]|1[0-9]|0?[1-9])))'
    # 备用正则，分隔符匹配，考虑没有分隔符情况，必须4位年,从1900-2999
    date_pattern1 = (
        r'(?:((?:19|2[0-9])(?:0[48]|[2468][048]|[13579][26]))|2[048]00)0?229|'
        r'(?:19|2[0-9])[0-9]{2}(?:(?:1[02]|0?[13578])31|'
        r'(?:1[0-2]|0?[13-9])(?:29|30)|'
        r'(?:1[0-2]|0?[1-9])(?:2[0-8]|1[0-9]|0?[1-9]))')

    date_reg = re.search(date_pattern, date_str)
    try:
        if date_reg:
            # 默认获取当前世纪的信息，年份前2位
            output_time = date_reg.group(0).replace('.', '-').replace('/', '-')
        # 第一种方式未获取成功
        else:
            output_time = None
    except Exception as e:
        output_time = time.strftime("%Y-%m-%d")
    return output_time


# 过滤空格
def filter_space_splash(content):
    #  |&ndash;|&mdash;|&#8210;|&#8211;|&#8212;|&#8213; transferred
    content = re.sub(r'[\u2010-\u2015\u207B\uFF0D]', '-', content)
    content = re.sub('\s', '', content, flags=re.U)
    return content


# 把字符串全角转半角
def strQ2B(ustring):
    """把字符串全角转半角"""
    rstring = ""
    for uchar in ustring:
        inside_code = ord(uchar)
        if inside_code == 0x3000:
            inside_code = 0x0020
        elif 0xFF01 <= inside_code <= 0xFF5E:  # 转完之后不是半角字符返回原来的字符
            inside_code -= 0xFEE0
        rstring += chr(inside_code)
    return rstring


# 把字符串半角转全角
def strB2Q(ustring):
    """把字符串半角转全角"""
    rstring = ""
    for uchar in ustring:
        inside_code = ord(uchar)
        if 0x0021 <= inside_code <= 0x007E:  # 不是半角字符就返回原来的字符
            inside_code += 0xFEE0
        elif inside_code == 0x0020:  # 除了空格其他的全角半角的公式为:半角=全角-0xfee0
            inside_code = 0x3000

        rstring += chr(inside_code)
    return rstring


# 该函数用来截取字符串左边
def get_str_left(string, repl, beg=0, end=None,
                 find_order=True,
                 out=False):  # 该函数用来截取字符串左边
    '''该函数用来截取字符串左边
        string 原始字符串
        repl 截取字符串
        beg 开始字符串
        end 结束字符串
        fing_order 为True表示从左边开始查找否则从右边开始查找
        out Ture 如果没有找到指定字符直接返回本生
        成功返回截取后的字符串 失败返回空
        例如
        get_str_left("1234567890", "5", 1 )
        返回 234
        '''
    if out:
        ret = string
    else:
        ret = ''
    if not isinstance(string, str) or not isinstance(repl, str):
        # 传入字段不是字符串 直接返回
        return ret
    if end is None:
        end = len(string)
    try:
        if find_order:
            result = string.find(repl, beg, end)
            if result == -1:
                # 表示没有找到传入的字符串直接返回
                return ret
            new_str = string[beg:result]
            return new_str
        else:
            result = string.rfind(repl, beg, end)
            if result == -1:
                # 表示没有找到传入的字符串直接返回
                return ret
            new_str = string[beg:result]
            return new_str
    except BaseException:
        return ret


# 该函数用来截取字符串右边
def get_str_right(string, repl, beg=0, end=None,
                  find_order=True,
                  out=False):  # 该函数用来截取字符串右边
    '''该函数用来截取字符串右边
        string 原始字符串
        repl 截取字符串
        beg 开始字符串
        end 结束字符串
        fing_order 为True表示从左边开始查找否则从右边开始查找
        成功返回截取后的字符串 失败返回空
        例如
        get_str_right("1234567890", "5", 1 )
        返回 67890
        '''
    if out:
        ret = string
    else:
        ret = ''
    if not isinstance(string, str) or not isinstance(repl, str):
        # 传入字段不是字符串 直接返回
        return ret
    if end is None:
        end = len(string)
    try:
        if find_order:
            result = string.find(repl, beg, end)
            if result == -1:
                # 表示没有找到传入的字符串直接返回
                return ret
            new_str = string[result + len(repl):end]
            return new_str
        else:
            result = string.rfind(repl, beg, end)
            if result == -1:
                # 表示没有找到传入的字符串直接返回
                return ret
            new_str = string[result + len(repl):end]
            return new_str
    except BaseException:
        return ret

# 该函数用来截取字符串中间(循环获取)
def get_str_mid_circle(string,
                repl_left,
                repl_right,
                beg=0,
                end=None,
                find_order=True,
                circle=True):
    '''该函数用来截取字符串中间
        string 原始字符串
        repl_left 截取字符串前边
        repl_right截取字符串后边
        beg 开始字符串
        end 结束字符串
        fing_order 为True表示从左边开始查找否则从右边开始查找
        circle  是否进行循环获取
        成功返回截取后的字符串 失败返回空
        例如
        get_str_mid("1234567890", "5", "7" )
        返回 列表
        '''
    if not isinstance(string, str) or not isinstance(
            repl_left, str) or not isinstance(repl_right, str)  or not repl_left or not repl_right:
        # 传入字段不是字符串 直接返回
        return []
    if end is None:
        end = len(string)
    result_list = []
    if find_order:
        pos = beg
    else:
        pos = end
    try:
        while True:

            if find_order:
                result1 = string.find(repl_left, pos, end)
                if result1 == -1:
                    # 表示没有找到传入的字符串直接返回
                    return result_list
                result2 = string.find(repl_right, result1 + len(repl_left), end)
                if result2 == -1:
                    # 表示没有找到传入的字符串直接返回
                    return result_list
                new_str = string[result1 + len(repl_left):result2]
                result_list.append(new_str)  # 匹配成功加入到返回列表
                pos = result2 + len(repl_right)  # 更新下次查找的起始位置

            else:
                # 从后往前匹配
                result1 = string.rfind(repl_right, beg, pos)
                if result1 == -1:
                    # 表示没有找到传入的字符串直接返回
                    return result_list
                result2 = string.rfind(repl_left, beg, result1)
                if result2 == -1:
                    # 表示没有找到传入的字符串直接返回
                    return result_list
                new_str = string[result2 + len(repl_left):result1]
                result_list.append(new_str)  # 匹配成功加入到返回列表
                pos = result2 - len(repl_left)  # 更新下次查找的起始位置


            if not circle:
                # 截取文本不循环 第一次运行完成后直接返回
                return result_list
    except BaseException:
        return result_list

# 该函数用来截取字符串中间
def get_str_mid(string,
                repl_left,
                repl_right,
                beg=0,
                end=None,
                find_order=True):
    '''该函数用来截取字符串中间
        string 原始字符串
        repl_left 截取字符串前边
        repl_right截取字符串后边
        beg 开始字符串
        end 结束字符串
        fing_order 为True表示从左边开始查找否则从右边开始查找
        成功返回截取后的字符串 失败返回空
        例如
        get_str_mid("1234567890", "5", "7" )
        返回 6
        '''
    result = get_str_mid_circle(string,
                                 repl_left,
                                 repl_right,
                                 beg=beg,
                                 end=end,
                                 find_order=find_order,
                                 circle=False)
    if result:
        return result[0]
    else:
        return ''


# 该函数用来截取字符串中间  模拟火车头 可以使用通配符(*)
def get_str_mid_wildcard(string,
                         repl_left,
                         repl_right,
                         beg=0,
                         end=None,
                         find_order=True,
                         escape=False):
    '''该函数用来截取字符串中间   可以使用通配符(*)
        string 原始字符串
        repl_left 截取字符串前边     可以使用通配符(*)
        repl_right截取字符串后边     可以使用通配符(*)
        beg 开始字符串
        end 结束字符串
        fing_order 为True表示从左边开始查找否则从右边开始查找
        escape   是否转换\r \t  如果为True 先进行替换 .replace('\r', '').replace('\t', ' ')
        成功返回截取后的字符串 失败返回空
        例如
        print(get_str_mid_wildcard("12345dfdf4fghfh6456fgfjhgiui6789yrtuyfeyu0", "5(*)4", "6(*)9" ))
        返回 fghfh


        从右边开始寻找
        get_str_mid_wildcard("12345dfdf4fghfh6456fgfjhgiui6789yrtuyfeyu67890", "45", "6789" ,find_order=False)
        返回 6fgfjhgiui6789yrtuyfeyu
        '''
    result = get_str_mid_wildcard_circle(string,
                                    repl_left,
                                    repl_right,
                                    beg=beg,
                                    end=end,
                                    find_order=find_order,
                                    circle=False)
    if result:
        ret_result = result[0]
    else:
        ret_result = ''
    if not ret_result and escape:
        # 提取失败  通过替换字符继续尝试
        # 该功能 如果检测没有效果晚点删除
        pass
    return ret_result

# 该函数用来截取字符串中间  模拟火车头 可以使用通配符(*)    循环获取
def get_str_mid_wildcard_circle(string,
                         repl_left,
                         repl_right,
                         beg=0,
                         end=None,
                         find_order=True,
                         circle=True,
                         escape=False):
    '''该函数用来截取字符串中间   可以使用通配符(*)
        string 原始字符串
        repl_left 截取字符串前边     可以使用通配符(*)
        repl_right截取字符串后边     可以使用通配符(*)
        beg 开始字符串
        end 结束字符串
        fing_order 为True表示从左边开始查找否则从右边开始查找
        circle 是否进行循环获取
        escape   是否转换\r \t  如果为True 先进行替换 .replace('\r', '').replace('\t', ' ')
        成功返回截取后的列表 失败返回空
        例如
        print(get_str_mid_wildcard("12345dfdf4fghfh6456fgfjhgiui6789yrtuyfeyu0", "5(*)4", "6(*)9" ))
        返回 ['fghfh']


        从右边开始寻找
        get_str_mid_wildcard("12345dfdf4fghfh6456fgfjhgiui6789yrtuyfeyu67890", "45", "6789" ,find_order=False)
        返回 ['6fgfjhgiui6789yrtuyfeyu']
        '''
    if not isinstance(string, str) or not isinstance(
            repl_left, str) or not isinstance(repl_right, str) or not repl_left or not repl_right:
        # 传入字段不是字符串 直接返回
        return []
    if not string or not repl_left or not repl_right:
        # 传入空字符  或者截取字符为空直接返回[]
        return []

    if escape:
        string = string.replace('\r', '').replace('\t', ' ')  # 对文本中换行符进行替换
        repl_left = repl_left.replace('\r', '').replace('\t', ' ')  # 对文本中换行符进行替换
        repl_right = repl_right.replace('\r', '').replace('\t', ' ')  # 对文本中换行符进行替换

    # 先检测是否存在通配符 如果不存在通配符直接使用 get_str_mid_circle处理速度会快

    if not locoy_reg_wildcard.search(repl_left) and not locoy_reg_wildcard.search(repl_right):
        result_list = get_str_mid_circle(string, repl_left, repl_right, end=end, find_order=find_order, circle=circle)
        return result_list

    repl_left_list = repl_left.split(r'(*)')  # 如果存在通配符 先进行分割处理
    repl_right_list = repl_right.split(r'(*)')  # 如果存在通配符 先进行分割处理
    left_pos = 0  # 截取str的左边位置
    right_pos = 0  # 截取str的右边位置
    if end is None:
        end = len(string)
    result_list = []
    try:
        while True:
            # 循环获取
            if find_order:
                for text in repl_left_list:
                    # 根据通配符分割后的列表 依次寻找分配后的文本  如果找不到直接返回  直到找到最后一个词  并且记录位置
                    # 右边文本也是如此 然后截取两个位置之间的文本
                    if text == '':
                        # 如果分割后的文本为空直接跳过  5(*)    (*)2     例如这几种情况 会出现分割出来的文本为空
                        pass
                    else:
                        result = string.find(text, beg, end)
                        if result == -1:
                            # 表示没有找到传入的字符串直接返回
                            return result_list
                        left_pos = result + len(text)
                        beg = left_pos

                for text in repl_right_list:
                    # 根据通配符分割后的列表 依次寻找分配后的文本  如果找不到直接返回  直到找到最后一个词  并且记录位置
                    # 右边文本也是如此 然后截取两个位置之间的文本
                    if text == '':
                        # 如果分割后的文本为空直接跳过  5(*)    (*)2     例如这几种情况 会出现分割出来的文本为空
                        pass
                    else:
                        result = string.find(text, beg, end)
                        if result == -1:
                            # 表示没有找到传入的字符串直接返回
                            return result_list
                        if right_pos == 0:
                            # 表示这个值还是初始化  所以复制  因为右边文本是记录 第一个字符的位置
                            right_pos = result
                        beg = result + len(text)

                new_str = string[left_pos:right_pos]
                result_list.append(new_str)
                right_pos = 0  # 记录初始化的位置 方便循环匹配

            else:
                # 因为是从右边开始的 所以首先要把字符创列表进行翻转
                repl_left_list.reverse()
                repl_right_list.reverse()

                for text in repl_right_list:
                    # 根据通配符分割后的列表 依次寻找分配后的文本  如果找不到直接返回  直到找到最后一个词  并且记录位置  因为是倒着寻找
                    # 所有从右边开始
                    if text == '':
                        # 如果分割后的文本为空直接跳过  5(*)    (*)2     例如这几种情况 会出现分割出来的文本为空
                        pass
                    else:
                        result = string.rfind(text, beg, end)
                        if result == -1:
                            # 表示没有找到传入的字符串直接返回
                            return result_list
                        right_pos = result
                        end = right_pos

                for text in repl_left_list:
                    # 根据通配符分割后的列表 依次寻找分配后的文本  如果找不到直接返回  直到找到最后一个词  并且记录位置
                    # 右边文本也是如此 然后截取两个位置之间的文本
                    if text == '':
                        # 如果分割后的文本为空直接跳过  5(*)    (*)2     例如这几种情况 会出现分割出来的文本为空
                        pass
                    else:
                        result = string.rfind(text, beg, end)
                        if result == -1:
                            # 表示没有找到传入的字符串直接返回
                            return result_list
                        if left_pos == 0:
                            # 表示这个值还是初始化  所以复制  从右边开始寻找  找到的第一个 就是最右边的字符
                            left_pos = result + len(text)
                        end = result

                new_str = string[left_pos:right_pos]
                result_list.append(new_str)
                left_pos = 0  # 记录初始化的位置 方便循环匹配

            if not circle:
                # 不进行循环 直接退出
                return result_list
    except BaseException:
        return []

# 用来截取根本中间  采用正则的方式  支持多个文本标识  两个文本之间用| 分割
def get_str_mid_reg(string,
                    repl_left,
                    repl_right,
                    beg=None,
                    end=None,
                    escape=True):
    '''string 原始字符串
        repl_left 截取字符串前边     可以使用通配符(*)  最好别使用通配符
        repl_right截取字符串后边     可以使用通配符(*)
        beg 开始字符串
        end 结束字符串
        escape 是否进行转义  默认会把前面文本跟后面文本进行正则转义  如果不转义  前后截取必须是正确的正则表达式
        circle 默认不循环'''
    result = get_str_mid_reg_circle(string,
                    repl_left,
                    repl_right,
                    beg=beg,
                    end=end,
                    escape=escape,
                    circle=False)
    if result:
        return result[0]
    else:
        return ''

# 用来截取根本中间  采用正则的方式  支持多个文本标识  两个文本之间用| 分割
def get_str_mid_reg_circle(string,
                    repl_left,
                    repl_right,
                    beg=None,
                    end=None,
                    escape=True,
                    circle=True):
    '''string 原始字符串
        repl_left 截取字符串前边     可以使用通配符(*)  最好别使用通配符
        repl_right截取字符串后边     可以使用通配符(*)
        beg 开始字符串
        end 结束字符串
        escape 是否进行转义  默认会把前面文本跟后面文本进行正则转义  如果不转义  前后截取必须是正确的正则表达式
        circle 是否循环匹配 循环匹配就用finditer
        '''
    # 先把传入文本转换成正则表达式  前后截取的关键词中不得包含|  如果存在必须用 \|转义 因为是调用正则来进行匹配的
    if not isinstance(string, str) or not isinstance(
            repl_left, str) or not isinstance(repl_right, str) or not repl_left or not repl_right:
        # 传入字段不是字符串 直接返回
        return []
    result_list = []
    try:
        if escape:
            # 进行转义操作
            new_repl_left = reg_escape.sub(r'\\\1',
                                           repl_left)  # 把传入的待替换的文本进行正则转义
            new_repl_left = new_repl_left.replace(r'\|', r'|')  # 把转义的|替换回来
            new_repl_left = new_repl_left.replace(r'\(\*\)',
                                                  r'[\s\S]*?')  # 把通配符(*)进行正则化
            new_repl_right = reg_escape.sub(r'\\\1',
                                            repl_right)  # 把传入的待替换的文本进行正则转义
            new_repl_right = new_repl_right.replace(r'\|', r'|')  # 把转义的|替换回来
            new_repl_right = new_repl_right.replace(
                r'\(\*\)', r'[\s\S]*?')  # 把通配符(*)进行正则化
        else:
            new_repl_left = repl_left.replace(r'\(\*\)',
                                              r'[\s\S]*?')  # 把通配符(*)进行正则化
            new_repl_right = repl_right.replace(r'\(\*\)',
                                                r'[\s\S]*?')  # 把通配符(*)进行正则化
        text = r')(?<content>[\s\S]*?)(?:'
        reg_text = ''.join(('(?:', new_repl_left, text, new_repl_right, r')'))
        if not circle:
            # 不进行循环获取
            ret_status = re.search(reg_text, string, pos=beg, endpos=end)
            if ret_status is None:
                # 表示没有找到对应的文本  直接返回‘’
                return result_list
            ret_text = ret_status.groups('content')[0]
            result_list.append(ret_text)
        else:
            ret_list = re.finditer(reg_text, string, pos=beg, endpos=end)
            if not ret_list:
                return result_list
            for data in ret_list:
                ret_text = data.groups('content')[0]
                result_list.append(ret_text)
        return result_list
    except BaseException:
        return []

# 传入文本  正则表达式进行文本提取
def get_str_reg(string, pattern):
    '''string  原始文本
        pattern  正则表达式
        格式：正则前字符串(?<content>[\w\W]*?)正则后字符串,其中content是程序用来引用的。'''
    result = get_str_reg_circle(string, pattern, circle=False)
    if result:
        return result[0]
    else:
        return ''

# 传入文本  正则表达式进行文本提取   (循环获取)
def get_str_reg_circle(string, pattern, circle=True):
    '''string  原始文本
        pattern  正则表达式
        格式：正则前字符串(?<content>[\w\W]*?)正则后字符串,其中content是程序用来引用的。
        返回一个list'''
    result_list = []
    if not isinstance(string, str) or not isinstance(pattern, str):
        # 传入字段不是字符串 直接返回
        return result_list
    try:
        # pattern =
        # pattern.replace(r'''(?<content>''',r'''(?P<content>''')#替换c#的分组名
        # 转换成python 能识别的
        if circle:
            result = re.finditer(pattern, string)
        else:
            result = re.search(pattern, string)

            result = [result]  # 加入到列表 变成可迭代的 保证跟finditer 返回的一致


        if not result :
            # 表示没有找到对应的文本  直接返回‘’
            return result_list
        for each in result:
            ret_text = each.group('content')
            result_list.append(ret_text)
        return result_list
    except BaseException:
        return result_list


# 传入字符串返回MD5  默认flag=True  返回32位哈希  如果flag=False  则返回16位的MD5
def str_to_md5(text, flag=True):
    if not isinstance(text, str):
        # 传入字段不是字符串 直接返回
        return ''
    text = hashlib.md5(text.encode('utf-8')).hexdigest()
    if flag:
        return text
    else:
        return text[8:-8]

def simhash_distance(first, another, f=64):
    """`f` is the dimensions of fingerprints
       first  两个需要对比的哈希值
       first another 两个哈希值 int"""
    assert isinstance(first, int) and isinstance(another, int)

    x = (first ^ another) & ((1 << f) - 1)
    ans = 0
    while x:
        ans += 1
        x &= x - 1
    return ans

def get_simhash(content):
    """
    传入字符串  生成整数型哈希值
    :param content: 传入字符串
    :return: 返回int类型 如果hash失败直接返回0
    """
    try:
        if not isinstance(content, str):
            return 0
        s = Simhash(content)
        values = s.value
    except Exception as e:
        values = 0
    return values


# 把文本转换成16位的哈希值 并且在前面加上_
def get_task_hash(text):
    '''传入  参数  或者标签:XXX  生成对应的hash
    把文本转换成16位的哈希值 并且在前面加上_'''
    new_rule_md5 = str_to_md5(text, flag=False)  # Itool模块中定义的方法
    return ''.join(('_', new_rule_md5))


# 传入文本然后把跟正则有关的字符都进行转义  防止拼接正则表达式的时候出现错误
def str_escape(reg_text):
    '''原始文本   返回转义好的文本'''
    ret_text = reg_escape.sub(r'\\\1', reg_text)  # 转义正则表达式
    return ret_text


# 字符串替换 支持通配符(*)  [参数]  [参数1] 模拟火车头的替换功能 通过正则实现
def str_replace_wildcard(text, old, new):
    '''old 原始字符串  模拟火车头 支持(*)通配符   [参数]'''
    if not isinstance(text, str) or not isinstance(old, str) or not isinstance(
            new, str):
        # 传入字段不是字符串 直接返回
        return ''
    # 先检测是否存在通配符 如果不存在通配符直接使用replace操作
    if not locoy_reg_wildcard.search(old):
        ret_text = text.replace(old, new)
        if ret_text == text and RE_CHAR.search(old) and RE_CHAR.search(text):
            # 替换失败 检测是否存在 \r\n 等特殊字符
            old = old.replace('\r', '').replace('\t', ' ')  # 对文本中换行符进行替换
            new_text = text.replace('\r', '').replace('\t', ' ')
            ret_text = new_text.replace(old, new)
        return ret_text

    try:
        old_text = reg_escape.sub(r'\\\1', old)  # 把传入的待替换的文本进行正则转义
        # old_text = re.escape(old)  # 转义
        old_text = old_text.replace(r'\(\*\)', r'[\s\S]*?')  # 由于经过转义  把通配符进行转换
        old_text = old_text.replace(r'\[参数\]',
                                    r'([\s\S]*?)')  # 由于经过转义  把通配符进行转换
        new_text = re.sub(r'\[参数(\d+?)\]', r'\\\1',
                          new)  # 转换成相应的正则替换文本   \\\1  就是获取分组1的值
        if old_text[-10:] == r'([\s\S]*?)':
            # 如果最后一个懒惰匹配   直接修改为贪婪匹配  否则表达式就没有意义
            old_text = ''.join((old_text[:-10], '([\s\S]*)'))
        if old_text[-8:] == r'[\s\S]*?':
            # 如果最后一个懒惰匹配   直接修改为贪婪匹配  否则表达式就没有意义
            old_text = ''.join((old_text[:-8], '[\s\S]*'))

        if "(*)" in old[:3] or '[参数]' in old[:4]:
            # 替换规则以(*) [参数] 开头 只进行一次替换
            ret_text = re.sub(old_text, new_text, text, count=1)
        else:
            ret_text = re.sub(old_text, new_text, text)
        return ret_text
    except BaseException:        # 如果出现异常直接返回原始字符串
        return None


# 过滤传入文本的html标签   &nbsp;|&quot;|&rdquo;|amp;|&gt;|&lt;  所有空格
def tag_filter(content, flag=0):
    """flag 0 为默认  1 专门跟火车头的全选一致"""
    if not isinstance(content, str):
        # 传入字段不是字符串 直接返回
        return ''
    if flag == 0:
        ret_text = re.sub(r'<[^>]*>|&nbsp;|&quot;|&rdquo;|amp;|&gt;|&lt;|\r|\n|\t', '', content)
    else:
        ret_text = re.sub(r'<[^>]*>|&nbsp;|\r|\n|\t|  ', '', content)
    return ret_text.strip()

def tag_close_filter(content):
    """检测是否存在不闭合标签  不闭合标签会自动删除

    ng-if="company.baseInfo.industry" class="ng-binding ng-scope">
                            <span class="c8">行业：</span>科技推广和应用服</span


    会自动删除不闭合标签
    （ng-if="company.baseInfo.industry" class="ng-binding ng-scope">）

    （</span）

    为防止误操作  检测<  > 前后不得存在中文 否则也不删除

    eg:        </span>科技推广和应用服<测试/span

    <测试/span  这个不闭合标签还是不会被删除


    """
    if not isinstance(content, str):
        # 传入字段不是字符串 直接返回
        return ''

    return RE_REPLACE_TABLE.sub('', content)


def clean_display_none(html):
    """清除 style 为display: none 的标签 删除整个节点
        上述标签页面上不展示  通常都是些垃圾数据"""
    if not isinstance(html, str):
        return html
    ret_iter = RE_DISPLAY_NONE.finditer(html)
    temp_html = html
    for each in ret_iter:
        start_pos = each.span()[0]
        end_pos = each.span()[1]
        end_str = r'</' + each.groups()[0]  # 生成闭合标签
        start_str = r'<' + each.groups()[0]  # 生成起始标签 防止标签嵌套
        ret = html.find(end_str, end_pos)  # 寻找闭合标签位置
        if ret == -1:
            continue
        temp_text = html[end_pos:ret]
        count = temp_text.count(start_str)  # 检测是否存在标签嵌套
        if count > 0:
            for _ in range(count):
                pos = ret + len(end_str)
                ret = html.find(end_str, pos)
                if ret == -1:
                    break
        pos = ret + len(end_str)  # 生成闭合标签当前位置 继续寻找结束 > 位置
        ret = html.find('>', pos)
        if ret == -1:
            continue
        pos = ret + 1
        str_len = pos - start_pos
        temp_html = temp_html.replace(html[start_pos:pos], ' ' * str_len)

    return temp_html




# 检测内容必须包含  如果存在返回true   否则返回false   传入类型错误 会返回None   支持火车头的(*) 通配符
# 两个关键词之间用 | 分割
def content_must(rules, content):
    if not isinstance(rules, str) or not isinstance(content, str):
        # 传入字段不是字符串 直接返回
        return None
    temp_text = reg_escape.sub(r'\\\1', rules)  # 把传入的规则进行正则转义
    temp_text = temp_text.replace(r'\(\*\)', '(?:.*?)').replace(r'\|', '|')
    ret_status = re.search(temp_text, content)
    if ret_status is None:
        # 表示正则匹配失败  直接返回false
        return False
    else:
        return True


# 检测内容不得包含  如果存在返回false   否则返回true  支持火车头的(*) 通配符   两个关键词之间用 | 分割
def content_forbid(rules, content):
    if not isinstance(rules, str) or not isinstance(content, str):
        # 传入字段不是字符串 直接返回
        return None
    ret_status = content_must(rules, content)
    if ret_status is None:
        # 表示传入的类型错误直接返回
        return ret_status
    elif ret_status:
        return False
    else:
        return True


# 拼接url 传入原网址  待拼接网址
def build_url(base, url):
    """Build the actual URL to use."""

    # Support for unicode domain names and paths.
    if not url or not base:
        return ''

    url1 = urljoin(base, url)
    arr = urlparse(url1)
    path = normpath(arr[2])
    new_url = urlunparse((arr.scheme, arr.netloc, path, arr.params, arr.query,
                       arr.fragment))
    if url and r'/' in url[-1]:
        new_url = new_url + '/'
    return new_url


# 进行base 编解码
def base64_encode(doc):
    try:
        doc = base64.encode(doc)
    except BaseException:
        pass
    return doc


def base64_decode(doc):
    try:
        doc = base64.decode(doc)
    except BaseException:
        pass
    return doc


# 进行html 编解码
def html_encode(doc):

    return doc


def html_decode(doc):
    html_parser = HTML_PARSER.HTMLParser()
    doc = html_parser.unescape(doc)
    return doc


# 进行网址的编解码
def url_quote(s, encodeing='utf-8', errors=None, safe=':/'):

    result = urllib.parse.quote(s, encoding=encodeing, safe=safe, errors=errors)
    #result = urllib.parse.quote_plus(s,encoding=encodeing,safe=':/')
    return result


_hexdig = '0123456789ABCDEFabcdef'
_hextobyte = None


def unquote_to_bytes(string, encoding='utf-8'):
    """unquote_to_bytes('abc%20def') -> b'abc def'."""
    # Note: strings are encoded as UTF-8. This is only an issue if it contains
    # unescaped non-ASCII characters, which URIs should not.
    if not string:
        # Is it a string-like object?
        string.split
        return b''
    if isinstance(string, str):
        string = string.encode(encoding, errors='replace')
    bits = string.split(b'%')
    if len(bits) == 1:
        return string
    res = [bits[0]]
    append = res.append
    # Delay the initialization of the table to not waste memory
    # if the function is never called
    global _hextobyte
    if _hextobyte is None:
        _hextobyte = {(a + b).encode(): bytes([int(a + b, 16)])
                      for a in _hexdig for b in _hexdig}
    for item in bits[1:]:
        try:
            if len(item) == 5:
                # try unicode
                try:
                    text = b'\\' + item
                    text = text.decode('raw_unicode_escape').encode('utf-8')
                    append(text)
                    continue
                except BaseException:
                    pass
            # append(_hextobyte[item])
            append(_hextobyte[item[:2]])
            append(item[2:])
        except KeyError:
            append(b'%')
            append(item)
    return b''.join(res)


re_base64 = re.compile(r'[^a-zA-Z0-9+=/]')


def url_unquote(s, encodeing='utf-8'):
    if not s:
        return s
    status = re_base64.search(s)
    if status:
        # 如果能够匹配到base64之外的字符 就说明没有进行编码
        data = s.encode(encodeing, errors='replace')
    else:
        try:
            data = base64.decodebytes(s.encode(encodeing, errors='replace'))
        except BaseException:
            data = s.encode(encodeing, errors='replace')
    result = unquote_to_bytes(data).decode(encodeing, errors='replace')
    #result = urllib.parse.unquote(data,encoding=encodeing)
    return result


# 把字符串的post 数据转换成dict
def post_data_to_dict(content):
    temp_dict = dict()
    ret_list = content.split('&')
    for data in ret_list:
        ret = data.split('=')
        key = ret[0]
        value = ret[1]
        temp_dict[key] = value
    return temp_dict


##########火车头规则解析   开始#########
locoy_reg_rule = re.compile(r'\[(参数\d*|标签:.*?)\]')  # # 匹配参数  标签
locoy_reg_rule1 = re.compile(r'\\\[(_[a-z0-9]{16})\\\]')  # # 匹配任务编号
locoy_reg_wildcard = re.compile(
    r'(\[参数\d*\]|\[标签:[^\]]*?\]|\(\*\))')  # # 匹配参数  标签
locoy_reg_wildcard1 = re.compile(
    r'((\[参数\d*\]|\[标签:[^\]]*?\]|\(\*\)){2,})')  # # 检测是否存在重合的标签
reg_parse_url = re.compile(
    r'<(.{1,10}?),(.{1,10}?),(.{1,10}?)(?:,(.{1,10}?))?(?:,(.{1,10}?))?(?:,(.{1,10}?))?>'
)  # 匹配网址规则
locoy_reg_url_type0 = re.compile(
    r'''href\s?=\s?(['" ])(.{1,1024}?)\1''', flags=2)


# 火车头规则转换成字符串查找的方式 防止使用正则匹配通配符过多导致的死循环
def locoy_rule_parse_str(content, script_rule, flag=0, count=None):
    '''content  传入的原始字符串
       script_rule  火车头的规则  <li><span>[标签:发布时间]</span><a href=[参数] title=[标签:标题] target=_blank>
        flag      flag=0  从前往后匹配   flag=1 从后往前匹配
        count     默认循环匹配出所有结果 也可以指定匹配的结果数量

         print(locoy_rule_parse_str('==123==456===789===4546==hhtrt====ghg====rt==tyt===yt===ty===','==[标签:标题12]==[参数]=='))
         返回 [{'[标签:标题12]': '123', '[参数1]': '456'}, {'[标签:标题12]': '=4546', '[参数1]': 'hhtrt'}, {'[标签:标题12]': 'ghg', '[参数1]': ''}, {'[标签:标题12]': 'tyt', '[参数1]': '=yt'}]'''
    if not isinstance(content, str) or not isinstance(script_rule, str):
        # 传入字段不是字符串 直接返回
        return []
    if not script_rule or not content:
        return []
    str_count = script_rule.count(r'[参数]')
    if str_count > 0:
        for num in range(str_count):
            # 把 href=[参数] title=[标签:标题] 替换成     # href=[参数1] title=[标签:标题]
            script_rule = script_rule.replace(
                r'[参数]', r'[参数{}]'.format(str(num + 1)), 1)

    temp_dict = {}
    ret_list = locoy_reg_wildcard1.findall(
        script_rule
    )  # 检测是否存在标签重合的情况  <span>(*)[参数]</span>  会自动替换成 <span>[参数]</span>
    for data in ret_list:
        text1 = data[0]
        text2 = data[1]
        ret_list1 = locoy_reg_wildcard.findall(text1)
        ret_list1.pop()  # 弹出最后一个 不做处理
        for data1 in ret_list1:
            if r'(*)' not in data1:
                temp_dict[data1] = ''

        script_rule = script_rule.replace(text1, text2, 1)

    wildcard_list = locoy_reg_wildcard.split(script_rule)
    '''经过上面的处理 会将

    [参数]<li><span>(*)[标签:发布时间][标签:标题12]</span><a href=[参数] title=[标签:标题] target=_blank[参数]>[标签:标题1]

    替换成

    [参数1]<li><span>[标签:标题12]</span><a href=[参数2] title=[标签:标题] target=_blank[参数3]>[标签:标题1]

    '''

    # 匹配规则开头跟结尾 是否存在 [参数][标签:xxx](*)

    # 如果存在直接赋值为空
    if wildcard_list[0] == '':
        if '标签:' in wildcard_list[1]:
            # (*)]&nbsp;<a href='[参数]' title='[标签:标题]'  解决(*) 开头被加入通配符 导致传递上下文
            temp_dict[wildcard_list[1].replace('[标签:', '').replace('[', '')
                      .replace(']', '')] = ''
        del wildcard_list[1]
        del wildcard_list[0]
    if wildcard_list[-1] == '':
        if '标签:' in wildcard_list[-2]:
            # (*)]&nbsp;<a href='[参数]' title='[标签:标题]'  解决(*) 开头被加入通配符 导致传递上下文
            temp_dict[wildcard_list[-2].replace('[标签:', '').replace('[', '')
                      .replace(']', '')] = ''
        del wildcard_list[-2]
        del wildcard_list[-1]

    if len(wildcard_list) < 3:
        # 如果分割的数量少于3个  直接返回 传入的规则存在问题
        return []
    if len(wildcard_list) % 2 == 0:
        # 如果长度为偶数 疑似转换错误 直接返回
        return []

    beg = 0  # 获取字符串的起始位置
    end = len(content)  # 字符串的结束位置
    pos = 0

    n = 0
    result_list = list()
    while True:
        label_dict = {}  # 临时保存标签的字典
        start_str = wildcard_list[0]  # 起始字符串
        result = content.find(start_str, pos, end)
        if result == -1:
            # 没有成功找到起始字符串
            return result_list
        start_pos = result + len(start_str)  # 开始位置
        pos = start_pos
        for num in range(int((len(wildcard_list) - 1) / 2)):
            label_str = wildcard_list[num * 2 + 1].replace('[标签:', '').replace(
                '[', '').replace(']', '')  # 要提取的标签名
            end_str = wildcard_list[num * 2 + 2]  # 结束的字符串
            result = content.find(end_str, pos, end)
            if result == -1:

                return result_list

            if r'(*)' not in label_str:
                label_dict[label_str] = content[pos:result]
            pos = result + len(end_str)
        label_dict.update(temp_dict)
        result_list.append(label_dict)
        n += 1
        if count and count <= n:
            # 达到指定提取次数 直接返回
            return result_list

    pass


def locoy_rule_parse(script_rules):
    '''把火车头的脚本规则解析成正则表达式   参数  标签会转换成16位的哈希值   为了防止正则分组名 命名失败 哈希值前面会加上_
    例如   '标题': '_311a3b5e76384fb4'
    参数  会自动在后面加上序号
    '参数1': '_678870e677b02735'
    '''
    if not isinstance(script_rules, str):
        return None
    rule_dict = dict()
    rule_list = list()
    # ret_rules = reg_escape.sub(r'\\\1', script_rules)  # 转义正则表达式
    rule_num = 0
    rule_list_re = locoy_reg_rule.findall(script_rules)
    # 先找出或者头中[参数][标签:XXX]等 通配符找出 并替换成哈希值    方便后面操作
    for rule in rule_list_re:
        if rule == '参数':
            rule_num += 1
            rule = ''.join((rule, str(rule_num)))
            rule_list.append({rule: get_task_hash(rule)})
            rule_dict[rule] = get_task_hash(rule)
        else:
            rule = rule.replace('标签:', '')
            rule_list.append({rule: get_task_hash(rule)})
            rule_dict[rule] = get_task_hash(rule)
    ret_text = script_rules
    for data in rule_list:
        key = list(data.keys())[0]
        value = list(data.values())[0]
        if '参数' in key:
            ret_text = ret_text.replace('[参数]', '[' + value + ']', 1)
        else:
            ret_text = ret_text.replace('[标签:' + key + ']', '[' + value + ']',
                                        1)
    ret_text = reg_escape.sub(r'\\\1', ret_text)  # 转义正则表达式
    ret_rules = locoy_reg_rule1.sub(r'(?<\1>[\s\S]{1,2000}?)' '', ret_text)
    ret_rules = ret_rules.replace(
        r'\(\*\)',
        r'[\s\S]{1,2000}?')  # 经过转义后 火车头的(*)被转换成\(\*\)  直接用\(\*\)  替换成[\s\S*?]
    return ret_rules, rule_dict


def locoy_builder_url_type0(start_url=None,
                            content=None,
                            forbid=None,
                            must=None):
    # 通过自动获取网址
    result_list = locoy_reg_url_type0.findall(content)
    data_list = []
    for data in result_list:
        temp_dict = dict()

        # 进行网址生成
        temp_url = data[1]

        if 'http' in temp_url:
            # 不用自动进行网址识别
            url = temp_url
        else:
            # 通过起始网址 自动补全链接
            url = build_url(start_url, temp_url.strip())
        if not url:
            # 表示传入的规则有问题 解析失败
            return
        if forbid:
            '''检测是否进行不得包含过滤'''
            status = content_forbid(forbid, url)
            if not status:
                # 返回false  即满足过滤条件
                # 直接返回继续
                continue
        if must:
            '''检测是否进行必须包含过滤'''
            status = content_must(must, url)
            if not status:
                # 返回false  即满足过滤条件
                # 直接返回继续
                continue
        # temp_dict['url'] = url  # 把生成的网址加入到临时字典中 并加入列表
        # data_list.append(temp_dict)
        data_list.append(url)
    # data_list = list(set(data_list))
    temp_list = []
    a = set()
    for url in data_list:
        # url = data.get('url')
        if url not in a:
            a.add(url)
            temp_list.append({'url': url})
    return temp_list


def locoy_builder_url_findstr(script_rules=None,
                              url_compile=None,
                              start_url=None,
                              content=None,
                              forbid=None,
                              must=None):
    '''通过查找字符串的方式匹配'''
    #script_rules = script_rules.replace('\n','\r\n')
    result_list = locoy_rule_parse_str(content, script_rules, flag=0)
    if not result_list:
        return result_list
    url_compile_list = locoy_reg_rule.findall(url_compile)
    data_list = []
    for data in result_list:
        temp_dict = dict()

        # 进行网址生成

        temp_text = copy.deepcopy(url_compile)
        for tmp_data in url_compile_list:
            if '标签' in tmp_data:
                tmp_data = tmp_data.replace('标签:', '')
            url_value = data.get(tmp_data)
            if not url_value:
                # 表示传入的规则有问题 解析失败
                # return data_list
                continue
            # 小面把实际链接中的[参数1] [标签:xxx]替换成真实的值

            if '参数' in tmp_data:
                temp_text = temp_text.replace('[' + tmp_data + ']', url_value,
                                              1)
                # del temp_dict[tmp_data]  # 删除字典中带参数的值  不需要返回给后面的正文页
            else:
                temp_text = temp_text.replace('[标签:' + tmp_data + ']',
                                              url_value, 1)

        if 'http' in url_compile[0:5]:
            # 不用自动进行网址识别
            url = temp_text
        else:
            # 通过起始网址 自动补全链接
            url = build_url(start_url, temp_text.strip())
        if not url:
            # 表示传入的规则有问题 解析失败
            return data_list
        if forbid:
            '''检测是否进行不得包含过滤'''
            # status = content_forbid(forbid, url)
            status = content_forbid(forbid, temp_text)  # 兼容火车头 网址未合并前判断是否不得包含
            if not status:
                # 返回false  即满足过滤条件
                # 直接返回继续
                continue
        if must:
            '''检测是否进行必须包含过滤'''
            status = content_must(must, url)
            if not status:
                # 返回false  即满足过滤条件
                # 直接返回继续
                continue
        temp_dict['url'] = url  # 把生成的网址加入到临时字典中 并加入列表
        for key, values in data.items():
            if '参数' not in key:
                temp_dict[key] = values
        data_list.append(temp_dict)
    return data_list


def locoy_builder_url_reg(script_rules=None,
                          url_compile=None,
                          start_url=None,
                          content=None,
                          forbid=None,
                          must=None):
    data_list = list()
    reg_text, rule_dict = locoy_rule_parse(
        script_rules)  # 转换的正则表达式   返回转换成的正则 跟字段名对应的字典
    # print(reg_text)
    # test = re.findall(reg_text,content)
    '''<li class='ico_pic_False'>
                            <span class='dateold'>(?<_f223876c24ee4f7e>[\s\S]*?)</span>
                            <a href='(?<_678870e677b02735>[\s\S]*?)' class='[\s\S]*?'
                                title='(?<_311a3b5e76384fb4>[\s\S]*?)'>[\s\S]*?</a> </li>'''
    # 上面多行的表达式在c#中能够正常的执行  python中执行失败 所以把空格都用\s替换了
    # 粗略估计应该是网页中的换行符使用\r\n而python中换行符用\n 导致的 解决的方案就是把\r\n 或者空格大于3的  替换成\s+?
    reg_text = re.sub(r'\s+', r'\s+?', reg_text)
    reg_text = reg_text.replace(r'\.', r'.')
    item_reg = re.finditer(reg_text, content)
    url_compile_list = locoy_reg_rule.findall(url_compile)

    for reg_obj in item_reg:
        temp_dict = dict()
        for key, value in list(rule_dict.items()):
            temp_text = reg_obj.group(value)
            temp_dict[key] = temp_text
        # 进行网址生成

        temp_text = copy.deepcopy(url_compile)
        for tmp_data in url_compile_list:
            if '标签' in tmp_data:
                tmp_data = tmp_data.replace('标签:', '')
            url_value = temp_dict.get(tmp_data)
            if not url_value:
                # 表示传入的规则有问题 解析失败
                return
            # 小面把实际链接中的[参数1] [标签:xxx]替换成真实的值

            if '参数' in tmp_data:
                temp_text = temp_text.replace('[' + tmp_data + ']', url_value,
                                              1)
                del temp_dict[tmp_data]  # 删除字典中带参数的值  不需要返回给后面的正文页
            else:
                temp_text = temp_text.replace('[标签:' + tmp_data + ']',
                                              url_value, 1)

        if 'http' in url_compile[0:5]:
            # 不用自动进行网址识别
            url = temp_text
        else:
            # 通过起始网址 自动补全链接
            url = build_url(start_url, temp_text.strip())
        if not url:
            # 表示传入的规则有问题 解析失败
            return
        if forbid:
            '''检测是否进行不得包含过滤'''
            status = content_forbid(forbid, url)
            if not status:
                # 返回false  即满足过滤条件
                # 直接返回继续
                continue
        if must:
            '''检测是否进行必须包含过滤'''
            status = content_must(must, url)
            if not status:
                # 返回false  即满足过滤条件
                # 直接返回继续
                continue
        temp_dict['url'] = url  # 把生成的网址加入到临时字典中 并加入列表
        data_list.append(temp_dict)
    return data_list


# 传入访问页面 指定位置信息 脚本规则  根据火车头信息自动提取参数 标签信息
def locoy_builder_url_rule(script_rules=None,
                           area_start=None,
                           area_end=None,
                           url_compile=None,
                           start_url=None,
                           content=None,
                           forbid=None,
                           must=None,
                           mode=True,
                           get_url_type=None,
                           encoding=None):
    """script_rules     火车头的脚本规则
        area_start         火车头区域选定前
        area_end         火车头区域选定后
        url_compile      火车头中 实际链接 用来生成网址
        start_url       火车头中 访问当前的网址  在生成网址的时候 如果没有检测到http开头 会进行自动补全
        content         访问start_url后返回的页面
        forbid         网址不得包含 支持通配符(*)  多个词用 |分割
        must          网址必须包含 支持通配符(*)  多个词用 |分割
        mode          默认为True  采用字符串匹配
        get_url_type   0 自动获取网址 1 根据规则获取网址
        """
    # if get_url_type == 1 and not script_rules or not start_url or not content or not url_compile :
    #     print('传入的参数不足')
    #     return
    re_result = re_base_url.findall(content)
    if re_result:
        # 正则能够获取到拼接的基础网址
        base_url = re_result[0][1]
        if not base_url:
            # 第一个分组获取网址失败  采用第二分组
            base_url = re_result[0][2].strip('"').strip("'")  # 去除首尾引号
        if 'http' in base_url[:4]:
            # 成功匹配到基础网址 替换传入的起始网址
            start_url = base_url



    if area_start and '\n' in area_start or area_end and '\n' in area_end or script_rules and '\n' in script_rules:
        # 如果规则中存在\n 换行符  就替换传入content中的\r\t
        content = content.replace('\r', '').replace('\t', ' ')
        area_start = area_start.replace('\r', '').replace('\t', ' ')
        area_end = area_end.replace('\r', '').replace('\t', ' ')

    if area_start and area_end:
        # 表示传入的网页需要进行截取操作
        content = get_str_mid_wildcard(content, area_start.strip(), area_end.strip())  # 去除首尾空
    if not content:
        # 范围提取失败
        return

    # 判断是否是自动获取网址
    if get_url_type == 0:
        result = locoy_builder_url_type0(
            start_url=start_url, content=content, forbid=forbid, must=must)
        return result

    if mode:
        result = locoy_builder_url_findstr(
            script_rules=script_rules,
            url_compile=url_compile,
            start_url=start_url,
            content=content,
            forbid=forbid,
            must=must)
        if not result and ('\t' in content or '\r' in content):
            # 原始网页存在\r \t 替换后再次尝试
            content = content.replace('\r', '').replace('\t', ' ')
            result = locoy_builder_url_findstr(
                script_rules=script_rules,
                url_compile=url_compile,
                start_url=start_url,
                content=content,
                forbid=forbid,
                must=must)
        # 临时解决方法 没有解决换行符问题
        if not result:
            if encoding and encoding.upper() != 'UTF-8' and RE_SPECIAL_CHAR.search(script_rules):
                # 规则中存在特殊字符 替换成. 进行匹配
                special_char = True
            else:
                special_char = False
        if not result and ('\n' in script_rules or ' ' in script_rules or '\r' in script_rules):
            label_all = locoy_reg_wildcard.findall(script_rules)
            if len(label_all) <= 7:
                # 如果规则中 万能标签过多 不执行  防止正则卡死
                result = locoy_builder_url_reg(
                    script_rules=script_rules,
                    url_compile=url_compile,
                    start_url=start_url,
                    content=content,
                    forbid=forbid,
                    must=must)

            if len(label_all) <= 8 and special_char and not result:
                #  如果存在特殊字符 再次进行尝试
                script_rules = RE_SPECIAL_CHAR.sub(r'.', script_rules)
                result = locoy_builder_url_reg(
                    script_rules=script_rules,
                    url_compile=url_compile,
                    start_url=start_url,
                    content=content,
                    forbid=forbid,
                    must=must)
    else:
        result = locoy_builder_url_reg(
            script_rules=script_rules,
            url_compile=url_compile,
            start_url=start_url,
            content=content,
            forbid=forbid,
            must=must)
    return result


def locoy_filter_IfEmptyDo(content, RegexContent, RegexCombine=None, circle=False):
    '''提取内容为空时重新提取   采用正则方式提取
        content   待提取的原始文本
        RegexContent  提取的正则表达式  如果不是正则表达式 就用替换的方式
        RegexCombine  如果采用正则匹配 就不用传入本参数'''
    if not content:
        # 如果传入的原始值为空  直接返回
        return content
    if r'''(?<content>''' not in RegexContent:
        if not RegexCombine:
            return ''
        if circle:
            result = locoy_filter_regex_circle(content, RegexContent, RegexCombine)
        else:
            result = locoy_filter_regex(content, RegexContent, RegexCombine)
    else:
        if circle:
            result = get_str_reg_circle(content, RegexContent)
        else:
            result = get_str_reg(content, RegexContent)
    return result


def locoy_filter_ReplaceFilter(content, old, new):
    '''内容替换
        content   待提取的原始文本
        old      替换前文本 支持通配符(*) [参数]
        new      替换后的内容'''

    if not content or not old:
        return content
    ret_content = str_replace_wildcard(content, old, new)

    if ret_content == content:
        # 内容替换失败检测是否存在\r \n \t 等字符的问题
        if '\r' in old or '\n' in old or '\t' in old:
            new_content = content.replace('\r', '').replace('\t', ' ')
            new_old = old.replace('\r', '').replace('\t', ' ')
            ret_content = str_replace_wildcard(new_content, new_old, new)
    return ret_content


def locoy_filter_RemoveHtmlFilter(content):
    '''HTML标签清除
        content   待提取的原始文本'''
    ret_content = tag_filter(content, flag=1)
    return ret_content


def locoy_filter_SubstringFilter(content, start, end, circle=False):
    '''内容截取
        content   待提取的原始文本
        start      开始字符串 支持通配符(*)
        end      结束字符串 支持通配符(*)
        circle     是否循环匹配  如果循环匹配返回list 不循环则返回字符串'''
    if circle:
        result = get_str_mid_wildcard_circle(content, start, end)
    else:
        result = get_str_mid_wildcard(content, start, end)
    if not result:
        if '\r' in start or '\t' in start or '\r' in end or '\t' in end:
            new_content = content.replace('\r', '').replace('\t', ' ')
            new_start = start.replace('\r', '').replace('\t', ' ')
            new_end = end.replace('\r', '').replace('\t', ' ')
            if circle:
                result = get_str_mid_wildcard_circle(new_content, new_start, new_end)
            else:
                result = get_str_mid_wildcard(new_content, new_start, new_end)
    return result


def locoy_filter_regex(text, old, new):
    '''old 原始字符串  模拟火车头 支持(*)通配符   [参数]'''
    result = locoy_filter_regex_circle(text, old, new, circle=False)
    if result:
        return result[0]
    else:
        return ''

def locoy_filter_regex_circle(text, old, new, circle=True):
    '''old 原始字符串  模拟火车头 支持(*)通配符   [参数]
       circle  是否进行循环获取'''
    result_list = []
    if not isinstance(text, str) or not isinstance(old, str) or not isinstance(
            new, str):
        # 传入字段不是字符串 直接返回
        return result_list
    try:
        old_text = reg_escape.sub(r'\\\1', old)  # 把传入的待替换的文本进行正则转义
        old_text = old_text.replace(r'\(\*\)', r'[\s\S]*?')  # 由于经过转义  把通配符进行转换
        old_text = old_text.replace(r'\[参数\]',
                                    r'([\s\S]*?)')  # 由于经过转义  把通配符进行转换
        # new_text =  reg_escape.sub(r'\\\1',old)#把传入的待替换的文本进行正则转义
        # new_text = re.sub(r'\[参数(\d+?)\]', r'\\\1', new)  # 转换成相应的正则替换文本
        # \\\1  就是获取分组1的值
        new_text = new
        if old_text[-10:] == r'([\s\S]*?)':
            # 如果最后一个懒惰匹配   直接修改为贪婪匹配  否则表达式就没有意义
            old_text = ''.join((old_text[:-10], '([\s\S]*)'))
        if old_text[-8:] == r'[\s\S]*?':
            # 如果最后一个懒惰匹配   直接修改为贪婪匹配  否则表达式就没有意义
            old_text = ''.join((old_text[:-8], '[\s\S]*'))
        if circle:
            result = re.finditer(old_text, text)
        else:
            result = re.search(old_text, text)
            result = [result]  # 加入到列表 变成可迭代的 保证跟finditer 返回的一致

        if result:
            for each in result:

                data_list = each.groups()
                for num, data in enumerate(data_list):
                    new_text = new_text.replace('[参数' + str(num + 1) + ']', data)
                result_list.append(new_text)
        return result_list

    except BaseException:
        return []


def locoy_filter_PureRegexFilter(content, old, new, flag=0):
    '''纯正则替换
        content   待提取的原始文本
        old      替换前文本 支持通配符(*) [参数]
        new      替换后的内容
        flag     默认为0 替换$1 $2  为\1 \2   由于c#的替换 $1 $2  python 中的替换规则 \1 \2 '''
    if flag == 0:
        new = reg_sub_to_py.sub(r'\\\1', new)
    ret_content = re.sub(old, new, content)
    return ret_content


def locoy_filter_FillEmpty(values, label):
    '''如果标签的内容为空 使用以下字符串作为缺省值  支持标签[标签:xxx]
        values   缺省值替换的内容
        label 如果传入清洗好的数据 就进行判断'''

    # 存在标签缺省值 如果传入了label 就进行查询 否则返回False
    result_list = []
    replace_values = values
    if label:
        ret_list = re.findall(r'\[标签:(.*?)\]', values)
        for data in ret_list:
            text = label.get(data)  # 从清洗好的数据中获取数据  如果获取失败 直接返回False
            if text is None:
                return False
            if isinstance(text,list):
                # 如果是list 类型 说明该字段是循环获取   目前只截取第一个值
                if text:
                    each = text[0]
                else:
                    each = ''
                # for each in text:
                #     replace_values = replace_values.replace(r'[标签:' + data + r']', each)
                #     result_list.append(replace_values)
                replace_values = replace_values.replace(r'[标签:' + data + r']', each)
            else:
                replace_values = replace_values.replace(r'[标签:' + data + r']', text)

        # if result_list:
        #     return result_list
    return replace_values


def locoy_filter_FillBothEnd(content, Start, End, EmptyNotFill=0):
    '''纯正则替换
        content   待提取的原始文本
        Start      内容前缀
        End      内容后缀
        EmptyNotFill     0 默认都加前后缀 1 如果内容为空则不添加前后缀'''
    if EmptyNotFill == 1 and not content:
        # 内容为空则不添加前后缀
        return ''
    ret_content = ''.join((Start, content, End))
    return ret_content



def locoy_data_filter(content, Filter, raw, label=None, circle=False):
    '''传入原始数据 需要过滤的方式 自动进行过滤
        content     原始数据
        Filter      过滤的列表
        raw         原始数据  当使用提取内容为空时 会自动重新提取
        label       清洗好的标签字典  当存在内容缺省值的时候 会自动检查所指定的标签是否存在 如果存在用指定的标签替换
        circle      是否进行循环获取
        '''
    '''
    [//上文截取的内容进入过滤器再进行过滤
{"filter_type":"if_empty_do"//提取内容为空时重新提取,
 "regex_content":"正则表达式  (?<content>[\s\S]*?)默认提取content",
 "regex_combine":"正则替换文本 [参数1][参数2] 替换RegexContent 中的参数"
},
{"filter_type":"replace_filter"//内容替换,
 "old":"替换前文本 支持通配符(*) [参数]",
 "new":"替换后的内容"
},
{"filter_type":"html_filter"//HTML标签清除,
 默认清除<>中的内容
},
{"filter_type":"substring_filter"//内容截取,
 "start":"开始字符串 支持通配符(*)",
 "end":"结束字符串 支持通配符(*)"
},
{"filter_type":"pure_regex_filter"//纯正则替换,
 "old":"待替换的正则表达式",
 "new":"替换后的表达式c#的替换 $1 $2  python 中的替换规则 \1 \2  在提取的时候需要进行转义"
},
{"filter_type":"fill_empty"//如果标签的内容为空 使用以下字符串作为缺省值  支持标签[标签:xxx],
 "fixdata":"空内容缺省值"
},
{"filter_type":"fill_both_end"//内容加前后缀,
 "start":"内容前缀",
 "end":"内容后缀 ",
 "empty_not_fill":0 默认都加前后缀 1 如果内容为空则不添加前后缀,
}
]'''
    if not Filter:
        # 不存在过滤规则直接返回
        return content
    temp_content = content
    for filter in Filter:
        filter_type = filter.get('filter_type')
        temp_list = []
        if not filter_type:
            # 无法识别过滤类型
            continue
        elif 'if_empty_do' in filter_type:
            # 提取内容为空时重新提取
            if not temp_content:
                # 首先确认当前内容是否为空
                regex_content = filter.get('regex_content')
                regex_combine = filter.get('regex_combine')
                temp_content = locoy_filter_IfEmptyDo(raw, regex_content,
                                                      regex_combine, circle=circle)
        elif filter_type == 'regex_filter':
            # 通过正则提取
            if temp_content:
                # 首先确认当前内容是否为空
                regex_content = filter.get('regex_content')
                regex_combine = filter.get('regex_combine')
                if isinstance(temp_content, list):
                    # 如果temp_content 在转换过程中类型变成了list  表示该标签采用了循环 并且设置了缺省值 或者进行了重新提取
                    for each in temp_content:
                        temp_data = locoy_filter_IfEmptyDo(each, regex_content,
                                                              regex_combine)
                        temp_list.append(temp_data)
                    temp_content = temp_list
                    continue
                temp_content = locoy_filter_IfEmptyDo(temp_content, regex_content,
                                                      regex_combine)
        elif 'replace_filter' in filter_type:
            # 内容替换
            if temp_content:
                # 首先确认当前内容是否为空
                old = filter.get('old')
                new = filter.get('new')
                if isinstance(temp_content,list):
                    # 如果temp_content 在转换过程中类型变成了list  表示该标签采用了循环 并且设置了缺省值 或者进行了重新提取
                    for each in temp_content:
                        temp_data = locoy_filter_ReplaceFilter(each, old, new)
                        temp_list.append(temp_data)
                    temp_content = temp_list
                    continue
                temp_content = locoy_filter_ReplaceFilter(
                    temp_content, old, new)
        elif 'html_filter' in filter_type:
            # HTML标签清除
            if temp_content:
                if isinstance(temp_content,list):
                    # 如果temp_content 在转换过程中类型变成了list  表示该标签采用了循环 并且设置了缺省值 或者进行了重新提取
                    for each in temp_content:
                        temp_data = locoy_filter_RemoveHtmlFilter(each)
                        temp_list.append(temp_data)
                    temp_content = temp_list
                    continue
                temp_content = locoy_filter_RemoveHtmlFilter(temp_content)
        elif 'substring_filter' in filter_type:
            # 内容截取
            if temp_content:
                # 首先确认当前内容是否为空
                start = filter.get('start')
                end = filter.get('end')
                if isinstance(temp_content,list):
                    # 如果temp_content 在转换过程中类型变成了list  表示该标签采用了循环 并且设置了缺省值 或者进行了重新提取
                    for each in temp_content:
                        temp_data = locoy_filter_SubstringFilter(each, start, end)
                        temp_list.append(temp_data)
                    temp_content = temp_list
                    continue
                temp_content = locoy_filter_SubstringFilter(
                    temp_content, start, end)
        elif 'pure_regex_filter' in filter_type:
            # 纯正则替换
            if temp_content:
                # 首先确认当前内容是否为空
                old = filter.get('old')
                new = filter.get('new')
                if isinstance(temp_content,list):
                    # 如果temp_content 在转换过程中类型变成了list  表示该标签采用了循环 并且设置了缺省值 或者进行了重新提取
                    for each in temp_content:
                        temp_data = locoy_filter_PureRegexFilter(each, old, new)
                        temp_list.append(temp_data)
                    temp_content = temp_list
                    continue
                temp_content = locoy_filter_PureRegexFilter(
                    temp_content, old, new)
        elif 'fill_empty' in filter_type:
            # 如果标签的内容为空 使用以下字符串作为缺省值
            if not temp_content:
                # 首先确认当前内容是否为空

                fixdata = filter.get('fixdata')
                if not fixdata:
                    continue
                ret_status = re.search(r'\[标签:(.*?)\]', fixdata)
                if ret_status and not label:
                    return False
                temp_content = locoy_filter_FillEmpty(fixdata, label)
                if temp_content is False:
                    return False
        elif 'fill_both_end' in filter_type:
            # 内容加前后缀
            if temp_content:
                # 首先确认当前内容是否为空
                start = filter.get('start')
                end = filter.get('end')
                empty_not_fill = filter.get('empty_not_fill')
                if isinstance(temp_content,list):
                    # 如果temp_content 在转换过程中类型变成了list  表示该标签采用了循环 并且设置了缺省值 或者进行了重新提取
                    for each in temp_content:
                        temp_data = locoy_filter_FillBothEnd(each, start, end, empty_not_fill)
                        temp_list.append(temp_data)
                    temp_content = temp_list
                    continue
                temp_content = locoy_filter_FillBothEnd(
                    temp_content, start, end, empty_not_fill)
        elif 'text_encode' in filter_type:
            #/进行编码指定   0   URLEncode 1   URLdecode 2   HTMLEncode 3   HTMLDecode 4   To base64 5   From base64 6   To js string 7   From Js String,
            if not temp_content:
                # 首先确认当前内容是否为空
                continue
            code_type = filter.get('code_type')
            code_type_encoding = filter.get('code_type_encoding')
            is_list = True
            if isinstance(temp_content, str):
                # 如果temp_content 在转换过程中类型变成了list  表示该标签采用了循环 并且设置了缺省值 或者进行了重新提取
                temp_content = [temp_content]
                is_list = False


            for each in temp_content:


                if code_type == 0:
                    temp_data = url_quote(
                        each, encodeing=code_type_encoding)
                elif code_type == 1:
                    temp_data = url_unquote(
                        each, encodeing=code_type_encoding)
                elif code_type == 2:
                    temp_data = html_encode(each)
                elif code_type == 3:
                    temp_data = html_decode(each)
                elif code_type == 4:
                    temp_data = base64_decode(each)
                elif code_type == 5:
                    temp_data = base64_decode(each)
                elif code_type == 6:
                    try:
                        temp = json.loads(each, strict=False)
                        temp_data = json.dumps(temp, ensure_ascii=False)
                    except Exception as e:
                        temp_data = url_unquote(each)
                        # temp_data = each
                elif code_type == 7:
                    try:
                        temp = json.loads(each, strict=False)
                        temp_data = json.dumps(temp, ensure_ascii=False)
                    except Exception as e:
                        temp_data = url_unquote(each)
                        # temp_data = each
                else:
                    # 目前没有处理js to string
                    raise
                temp_list.append(temp_data)

            if not is_list:
                # 如果temp_cotent原先是字符串类型的 则使用字符串类型进行返回
                temp_content = temp_data
            else:
                temp_content = temp_list


    # 返回过滤后的规则
    return temp_content

def locoy_relative_url(start_url, content):
    """
    :param start_url: 原始网址
    :param content: 需要补全网址的内容
    :return: 返回补全后的文本
    """
    if not start_url or not content:
        return content
    ret_list = re_relative_url.findall(content)
    new_content = content
    pos = 0 # 寻找的起始位置
    for data in ret_list:
        url = data[1]

        if not url:
            url = data[2]
        pos = new_content.find(url, pos)
        if ': void(0)' in url:
            pos += len(url)
            continue
        if len(url) < 25 and 'javascript' in url:
            #不是正确的网址 自动跳过
            pos += len(url)
            continue
        if 'http' in url[:5]:
            # 已经是绝对网址 跳过
            pos += len(url)
            continue
        try:
            new_url = build_url(start_url, url)
            if not new_url:
                continue
        except ValueError:
            # 网址拼接失败
            # <img src="file://C:\Users\hpdl1\AppData\Roaming\Tencent
            # \Users\262617590\QQ\WinTemp\RichOle\Q%BJW)A95V1([4JS5CY1M%8.png" />
            pos += len(url)
            continue

        re_url = re.escape(url)
        try:
            new_content = re.sub(re_url, new_url, new_content, count=1, pos=pos)
            pos += len(new_url)
        except Exception:
            # 替换失败直接跳过
            pos += len(url)
        #new_content = new_content.replace(url, new_url, count=1)
    return new_content

def locoy_extract_data_2(config):
    '''自定义固定格式获取数据 '''
    manual_type = config.get(
        'manual_type'
    )  # 自定义固定格式的数据  选择类型 0 固定的字符串 1系统时间 根据ManualTimeStr进行格式化 2 随机字符串 3 随机数字 4 随机抽取信息 5 获取10位的系统时间戳,
    if manual_type == 0:
        manual_string = config.get('manual_string')
        result = manual_string
    elif manual_type == 1:
        result = time.strftime("%Y-%m-%d", time.localtime(time.time()))
    else:
        return None
    return result


def locoy_extract_data(content, config, label=None, label_in_circle=0, label_circle=None, start_url=None):
    '''提取数据 并处理数据
    label 清洗好的字段字典
    label_in_circle  0 标签只匹配一次 1 标签循环匹配
    label_circle 获取全局的标签循环规则
    start_url 当前页的起始网址  用来对相对网址进行补全'''
    raw = content  # 复制一份原始数据
    get_data_type = config.get(
        'get_data_type'
    )  # 提取数据的方式  0 前后截取 1 正则提取 3 标签组合 4 正文提取（目前没有使用） 2 可视化提取（目前没有使用）

    if label_in_circle == 1 and label_circle:  # 获取全局的标签循环规则
        loop_add_new_record = label_circle.get('loop_add_new_record')
        # 0 标签循环添加为新记录 1 标签循环获取 用分隔符连接上下条数据
        fill_loop_with_first = label_circle.get('fill_loop_with_first')
        # 0 不勾选 1 勾选 循环不足时用第一条数据补全
        loop_join_code = label_circle.get('loop_join_code')
        # 标签循环分隔符   [换行] 需要替换成\n"
        loop_join_code = loop_join_code.replace('[换行]', '\n')
    else:
        loop_add_new_record = 1
        fill_loop_with_first = 0
        loop_join_code = ''

    if label_in_circle == 1:
        # 循环获取
        circle = True
    else:
        circle = False

    page_start_str = config.get('page_start_str')
    page_end_str = config.get('page_end_str')
    # 合并火车头多页
    if page_start_str and page_end_str:
        content = locoy_filter_SubstringFilter(content, page_start_str,
                                               page_end_str)  # 前后截取 提取
    if get_data_type == 0:
        start_str = config.get('start_str')
        end_str = config.get('end_str')
        result = locoy_filter_SubstringFilter(content, start_str,
                                              end_str, circle=circle)  # 前后截取 提取
    elif get_data_type == 1:
        regex_content = config.get('regex_content')
        regex_combine = config.get('regex_combine')
        result = locoy_filter_IfEmptyDo(
            content, regex_content, RegexCombine=regex_combine, circle=circle)  # 通过正则提取
    elif get_data_type == 3:
        merge_content = config.get('merge_content')  # 获取标签组合
        ret_status = re.search(r'\[标签:(.*?)\]', merge_content)
        if ret_status and not label:
            return False
        result = locoy_filter_FillEmpty(merge_content, label)
        if not result:
            return result
    else:
        return None  # 未知情况



    result_list = []
    Filter = config.get('filter')
    filter_status = False
    if not circle:
        # 不循环获取
        result = [result]  # 生成可迭代的 方便统一处理
    for each in result:
        result_data = locoy_data_filter(each, Filter, raw, label=label)
        if isinstance(result_data,list):
            # 返回list类型  存在缺省值且该标签需要循环
            result_list.extend(result_data)
            break
        if result_data is False:
            # 存在空内容缺省值或返回False
            return False
        not_null = config.get('not_null')  # 0 采集内容不得为空 1 可以为空
        content_must = config.get('content_must')  # 采集内容必须包含
        content_forbid = config.get('content_forbid')  # 采集内容不得包含
        length_filt_opertar = config.get('length_filt_opertar')  # 0 不进行内容长度的过滤  1 大于 2 小于 3 等于 4 不等于,
        length_filt_value = config.get('length_filt_value')  # 0 需要过滤的字符串长度 如果为0 不过滤,
        status = locoy_content_filter(
            result_data,
            LabelContentForbid=content_forbid,
            LabelContentMust=content_must,
            LabelNotNull=not_null,
            length_filt_opertar=length_filt_opertar,
            length_filt_value=length_filt_value)
        if status:
            # 如果返回Ture表示满足过滤条件
            filter_status = True
            continue
            # return 'filter'

        # "fill_relative_url": 0 默认不操作 1 将相对网址补全为绝对网址
        fill_relative_url = config.get('fill_relative_url')  # 检测是否进行相对网址自动补全
        label_name = config.get('label_name')
        if fill_relative_url == 1 or label_name in ['内容', '正文']:
            result_data = locoy_relative_url(start_url, result_data)


        result_list.append(result_data)

    if not result_list and filter_status:
        # 解析不了数据 并且标记位过滤 直接返回过滤
        return 'filter'
    if circle and loop_add_new_record == 1:
        # 循环获取标签 并且把循环出来的字段用指定字符串连接  当做标签不循环的方法来做
        result = loop_join_code.join(result_list)
        return result
    if not circle:
        # 不进行标签循环获取  返回的是str  否则返回的是一个list
        result = ''.join(result_list)
        return result

    return result_list


def locoy_get_post_data(parser_rule, content=None, post_num=None):
    '''如果规则指定post 访问 会调用本函数生成需要的post数据
        content  传入的原始数据  如果传入为空 默认第一次访问
        post_num   采用post 方法时 记录当前的分页值
        如果需要不需要post随机值  第一页就用post访问 如果存在 第一页则用get 访问'''
    post_data = parser_rule.get('post_data')
    post_hash_dic = parser_rule.get('post_hash_dic')  # post 随机值的获取
    post_start = parser_rule.get('post_start')  # post分页开始的页码--整数型
    post_end = parser_rule.get('post_end')  # post分页结束的页码--整数型

    if post_num is None:
        # 第一次调用  刚开始并不存在post_data
        post_num = post_start + 1  # 在第二次访问的时候访问的页码 自动加1
    else:
        post_num += 1
    if post_num > post_end:
        # 生成的post 分页大于了指定结束的分页  直接返回
        return {
            'post_data': '',
            "post_status": False,
            'post_num': post_num,
            'post_err': ''
        }
    if '[POST随机值' in post_data:
        # 根据PostHashDic  自动生成随机值
        post_err = ''
        for hash_dic in post_hash_dic:
            Name = hash_dic.get('name')
            Key = hash_dic.get('key')
            Value = hash_dic.get('value')
            post_value = get_str_mid_wildcard(content, Key, Value)
            if not post_value:
                # 在提取post随机值得时候提取失败   把失败信息写到err中
                post_err = 'Extract the random value fails'
            # post_value = post_value.replace('=', '%3d').replace(r'/', '%2f')  # 防止 = 对post 数据干扰
            post_value = url_quote(post_value, encodeing='utf-8', errors='replace')
            post_data = post_data.replace(Name, post_value)
        new_post_data = post_data.replace('[分页]', str(post_num))
        return {
            'post_data': new_post_data,
            "post_status": True,
            'post_num': post_num,
            'post_err': post_err
        }
    else:

        new_post_data = post_data.replace('[分页]', str(post_num))
        return {
            'post_data': new_post_data,
            "post_status": True,
            'post_num': post_num,
            'post_err': ''
        }


def locot_retry_label():
    '''处理火车中内容缺省值为[标签:xxx]  提取标签方式为标签作何的情况'''

def locoy_get_detail(content, parser_rule, url=None, pages_num=None):
    """content       原始的正文数据
       parser_rule   火车规则
       url           有些信息可能需要在网址中提取
       pages_num     标记当前详情页的分页数
       返回 清洗后的标签数据 """
    if not content or not parser_rule:
        return {}

    content = content.replace('\r', '').replace('\t', ' ')  # 对文本中换行符进行替换

    data_substring = parser_rule.get('data_substring')  # 如果设定了采集区域 就想进行范围截取
    if data_substring:
        start_str = data_substring.get('start_str')  # 区域开始
        end_str = data_substring.get('end_str')  # 区域结束
        content = locoy_filter_SubstringFilter(content, start_str,
                                               end_str)  # 前后截取 提取

    result_dict = dict()
    page_name = parser_rule.get('page_name')
    root_rule = parser_rule.get('root_rule')
    mult_pages = parser_rule.get('mult_pages')  # 检测是否存在多页的情况 如果存在生成相应的访问网址
    # 检测详情页是否存在分页的情况 如果存在提取相应的网址
    detail_pages = parser_rule.get('detail_pages')

    label_circle = parser_rule.get('label_circle')
    if label_circle:  # 获取全局的标签循环规则
        loop_add_new_record = label_circle.get('loop_add_new_record')
        # 0 标签循环添加为新记录 1 标签循环获取 用分隔符连接上下条数据
        fill_loop_with_first = label_circle.get('fill_loop_with_first')
        # 0 不勾选 1 勾选 循环不足时用第一条数据补全
        loop_join_code = label_circle.get('loop_join_code')
        # 标签循环分隔符   [换行] 需要替换成\n"
        loop_join_code = loop_join_code.replace('[换行]', '\n')
    else:
        loop_add_new_record = 1
        fill_loop_with_first = 0
        loop_join_code = ''
    retry_list = list()
    filter_status = False  # 标记是否手动过滤
    circle_status = False  # 标记是否存在字段循环获取
    for data in root_rule:
        label_in_page = data.get('label_in_page')  # 0 标签不在分页中匹配 1 标签在分页中匹配
        label_in_circle = data.get('label_in_circle')  # 0 标签只匹配一次 1 标签循环匹配
        if label_in_circle == 1:
            circle_status = True
        if pages_num and label_in_page == 0:
            # 解析的是分页 但是清洗的标签不需要再分页中获取 直接跳过
            continue
        from_url = data.get('from_url')  # 通过返回的content提取内容 1 通过网址提取内容
        if from_url == 0:
            temp_content = content
        else:
            temp_content = url
        label_name = data.get('label_name')
        if not label_name:
            # 如果标签名不存在 规则一定存在问题 直接返回{}
            return {}
        data_spider = data.get('data_spider')  # 0 通过采集获取数据 1 自定义固定格式的数据
        if data_spider == 0:
            result = locoy_extract_data(temp_content, data, label_in_circle=label_in_circle,
                                        label_circle=label_circle, start_url=url)  # 通过采集获取数据
            # 如果返回的是list 类型 就表示进行了标签循环匹配了
            if result is False:
                # 如果出现了 空内容缺省值 替换后的内容为[标签;xxx]等所有内容爬取完成后统一处理 保存一下当前处理规则
                retry_list.append({
                    'parser_rule': data,
                    'page_name': page_name,
                    'label_name': label_name,
                    'label_circle': label_circle,
                    'label_in_circle': label_in_circle
                })
                continue
            if result == 'filter':
                # 满足过滤条件
                result_dict = {}
                filter_status = True
                break

        else:
            result = locoy_extract_data_2(data)  # 提取 自定义固定格式的数据
        result_dict[label_name] = result
    result_dict.update({'url': url})

    #  先判断是否存在分页情况
    pages_data = []
    pages_url = []
    if detail_pages:
        pages_join_code = detail_pages.get('pages_join_code')  # 分页连接符
        pages_area_end = detail_pages.get('pages_area_end')  # 分页结束
        pages_area_start = detail_pages.get('pages_area_start')  # 分页起始分割
        pages_url_list_all = detail_pages.get(
            'pages_url_list_all')  # 0 全部列出模式 1 上下页模式
        get_pages_url_auto = detail_pages.get(
            'get_pages_url_auto')  # 0 自动识别 获取网址 1 手动填写分页获取规则
        max_pages = detail_pages.get('max_pages')  # 最大分页数

        pages_style = detail_pages.get('pages_style')  # 获取分页地址样式
        pages_combine = detail_pages.get('pages_combine')  # 获取分页组合网址

        pages_url_list = locoy_builder_url_rule(
            script_rules=pages_style,
            area_start=pages_area_start,
            area_end=pages_area_end,
            url_compile=pages_combine,
            start_url=url,
            content=content,
            get_url_type=get_pages_url_auto)  # 通过火车头规则解析出 url 列表

        if pages_num:
            pages_num += 1
        else:
            pages_num = 1

        if pages_num > 1 and pages_url_list_all == 0:
            # 当前的分页数大于1 说明处理的是分页爬取的内容  规则中又指定了 全部列出模式 就不进行网址的获取
            pages_status = False
        else:
            pages_status = True

        if pages_url_list and pages_status:
            for url_data in pages_url_list:
                tmp_url = url_data.get('url')
                if tmp_url:
                    pages_url.append(tmp_url)

                # 解析出下一页网址 判断是否全部列出
                if pages_url_list_all == 1:
                    break
            # 判断是否达到了最大的分页

            for data in pages_url:
                if pages_num <= max_pages or max_pages == 0:
                    # 满足分页条件 添加返回值
                    pages_data.append(
                        {'url': data,
                         'pages_join_code': pages_join_code,
                         'pages_num': pages_num}
                    )
                    pages_num += 1
                else:
                    break

    mult_page_list = []
    for rule in mult_pages:
        page_name = rule.get('page_name')
        mult_page = rule.get('mult_page')
        # 火车头目前支持从网址中进行替换 采用纯正则的方式 从原文中进行替换 "filter_type":"replace_filter"
        mult_page_url_from_html = mult_page.get(
            'mult_page_url_from_html')  # 0 从网址中替换出新的网址  1 从获取的内容中提取网址
        page_replace_url = mult_page.get('page_replace_url')
        page_replace_new = mult_page.get('page_replace_new')
        page_url_style = mult_page.get('page_url_style')
        page_url_combine = mult_page.get('page_url_combine')
        if mult_page_url_from_html == 0:
            # 从网址中提取
            temp_content = url
            if not page_replace_url and not page_replace_new:
                # 设置了从网址中提取但是没有设置提取规则 拿到的是原网址 直接跳过
                continue
            temp_url = locoy_filter_PureRegexFilter(
                temp_content, page_replace_url, page_replace_new)
            if url == temp_url:
                # 拼接的网址等于原始网址
                continue
        else:
            temp_content = content
            if not page_url_style and not page_url_combine:
                # 设置了从网址中提取但是没有设置提取规则 拿到的是原网址 直接跳过
                continue
            temp_url = locoy_filter_regex(temp_content, page_url_style,
                                          page_url_combine)
            if url == temp_url:
                # 拼接的网址等于原始网址
                continue
        if temp_url:
            temp_url = build_url(url, temp_url)  # 拼接出新的url
        mult_page_list.append({'url': temp_url})

    return {
        'detail_context': result_dict,
        'page_name': page_name,
        'retry_list': retry_list,
        'mult_page_list': mult_page_list,
        'pages_data': pages_data,
        'filter_status': filter_status,
        'circle_status': circle_status,
        'fill_loop_with_first': fill_loop_with_first
    }


def locoy_get_index(url, content, parser_rule, post_num=None, pages_num=None,encoding=None):
    '''传入原始数据 根据规则解析出网址
       如果是分页 再解析出分页网址
       如果用post 访问的 再解析出data
       url    原始网址
       content   原始网页
       parser_rule  解析规则
       post_num  采用post 方法时 记录当前的分页值
       pages_num  列表页采用翻页的方式访问时记录当前的翻页值
       '''
    http_method = parser_rule.get('http_method')
    area_start = parser_rule.get('area_start')  # 网址提取范围前
    area_end = parser_rule.get('area_end')  # 网址提取范围后
    url_style = parser_rule.get('url_style')  # 提取网址 标签 规则
    url_compile = parser_rule.get('url_compile')  # 网址实际连接
    url_forbid = parser_rule.get('url_forbid')  # 网址不得包含 支持通配符(*)  多个词用 |分割
    url_must = parser_rule.get('url_must')  # 网址必须包含 支持通配符(*)  多个词用 |分割
    get_url_type = parser_rule.get('get_url_type')  # 0 自动获取网址  1 通过规则获取网址

    list_page_data = locoy_builder_url_rule(
        script_rules=url_style,
        area_start=area_start,
        area_end=area_end,
        url_compile=url_compile,
        start_url=url,
        content=content,
        forbid=url_forbid,
        must=url_must,
        get_url_type=get_url_type,
        encoding=encoding)  # 通过火车头规则解析出 url 标签列表
    if list_page_data:
        # 用来判断获取的列表页是否为空  如果进行网址标题的过滤 返回的list_page_data
        # 可能也为空 这里加一个标识
        pages_count = len(list_page_data)
    else:
        pages_count = 0

    if list_page_data is None:
        # 传入的参数不足
        list_page_data = []
    add_label = parser_rule.get('add_label')  # 获取附加标签
    result_list = locoy_rule_parse_str(content, add_label, count=1)
    if add_label and not result_list and '\n' in content:
        # 提取失败 去除换行再次尝试
        new_content = content.replace('\r', '').replace('\t', ' ')
        result_list = locoy_rule_parse_str(new_content, add_label, count=1)
    if result_list:
        # 更新附加标签
        page_data = []
        for data in list_page_data:
            data.update(result_list[0])
            page_data.append(data)
        list_page_data = page_data
    else:
        if add_label:
            ret_list = locoy_reg_rule.findall(add_label)
            temp_dict = {}
            for each in ret_list:
                if '标签:' in each:
                    each = each.replace('标签:', '')
                    temp_dict[each] = ''
            page_data = []
            for data in list_page_data:
                data.update(temp_dict)
                page_data.append(data)
            list_page_data = page_data


    list_page_data = locoy_filter_list_label(list_page_data,
                                             parser_rule)  # 进行标签过滤

    if http_method == 1:
        # 采用post 需要生成下次访问的post值
        ret_result = locoy_get_post_data(
            parser_rule, content, post_num=post_num)  # 解析post数据
        return {'list_page_data': list_page_data, 'post': ret_result, 'pages_count': pages_count}

    # 如果执行到下面 说明采用get 访问 判断是否存在翻页 如果存在生成翻页连接
    pages_area_start = parser_rule.get('pages_area_start')  # 列表分页获取前  支持通配符(*)
    pages_area_end = parser_rule.get('pages_area_end')  # 列表分页获取后  支持通配符(*)
    pages_url_style = parser_rule.get(
        'pages_url_style'
    )  # 列表分页地址获取 在PagesAreaStart  PagesAreaEnd范围内获取指定规则 支持 [参数]
    pages_url_compile = parser_rule.get(
        'pages_url_compile')  # 列表分页网址  会自动提取PagesUrlStyle中的 [参数] 匹配
    pages_max = parser_rule.get('pages_max')  # 最多分页获取数，0为不限制  整数型
    if not pages_area_start or not pages_area_end:
        # pages_area_start 或 pages_area_end  为空 就不执行翻页获取操作
        next_pages = {
            "pages_status": False,
            'pages_num': pages_num,
            'next_url': ''
        }
        return {'list_page_data': list_page_data, 'next_pages': next_pages, 'pages_count': pages_count}
    if not pages_num:
        # 表示第一次执行分页操作
        pages_num = 0
    pages_num += 1
    if not pages_max:
        pages_max = 0
    elif pages_num > pages_max and pages_max > 0:
        # 当前访问的数量 大于最大的访问页数 直接返回 不再执行翻页操作
        next_pages = {
            "pages_status": False,
            'pages_num': pages_num,
            'next_url': ''
        }
        return {'list_page_data': list_page_data, 'next_pages': next_pages, 'pages_count': pages_count}

    if pages_url_style and pages_url_compile:
        # 如果列表分页获取存在信息 就执行分页获取网址的操作
        next_page_result = locoy_builder_url_rule(
            script_rules=pages_url_style,
            area_start=pages_area_start,
            area_end=pages_area_end,
            url_compile=pages_url_compile,
            start_url=url,
            content=content)
        if not next_page_result:
            # 无法解析下一页网址 直接返回
            next_pages = {
                "pages_status": False,
                'pages_num': pages_num,
                'next_url': ''
            }
            return {'list_page_data': list_page_data, 'next_pages': next_pages, 'pages_count': pages_count}
        next_url = next_page_result[0].get('url')
        next_pages = {
            "pages_status": True,
            'pages_num': pages_num,
            'next_url': next_url
        }

    else:
        next_pages = {
            "pages_status": False,
            'pages_num': pages_num,
            'next_url': ''
        }

    return {'list_page_data': list_page_data, 'next_pages': next_pages, 'pages_count': pages_count}


def locoy_filter_list_label(Label, parser_rule):
    '''对传入的列表页信息进行过滤  传入的是一个字典 ListLable 传入的过滤规则
    Label   标签列表'''
    list_label = parser_rule.get('list_label')
    label_dict = dict()
    for data in list_label:
        label_name = data.get('label_name')
        label_dict[label_name] = data
    temp_list = list()
    for temp_data in Label:


        fildered = False
        for key, data in list(label_dict.items()):
            content = temp_data.get(key)  # 从正文页提取的标签中获取过滤的字段名 如果不存在 直接跳出循环
            if not content:
                continue
            Filter = data.get('filter')
            result = locoy_data_filter(content, Filter, content)
            # result = locoy_extrac_data(content, data)  # 通过采集获取数据
            not_null = data.get('not_null')  # 0 采集内容不得为空 1 可以为空
            content_must = data.get('content_must')  # 0 内容过滤必须包含
            content_forbid = data.get('content_forbid')  # 内容过滤不得包含
            length_filt_opertar = data.get('length_filt_opertar')  # 0 不进行内容长度的过滤  1 大于 2 小于 3 等于 4 不等于,
            length_filt_value = data.get('length_filt_value')  # 0 需要过滤的字符串长度 如果为0 不过滤,
            status = locoy_content_filter(
                result,
                LabelContentForbid=content_forbid,
                LabelContentMust=content_must,
                LabelNotNull=not_null,
                length_filt_opertar=length_filt_opertar,
                length_filt_value=length_filt_value
            )
            if status:
                # 如果返回Ture表示满足过滤条件
                fildered = True
                break
            if not result:
                break
            temp_data[key] = result
        if not fildered:
            # 返回不许要过滤的数据
            temp_list.append(temp_data)
    return temp_list

    pass


def locoy_content_filter(content,
                         LabelNotNull=None,
                         LabelContentMust=None,
                         LabelContentForbid=None,
                         length_filt_opertar=0,
                         length_filt_value=0):
    """对处理后的数据进行过滤
        LabelNotNull   0 采集内容不得为空 1 可以为空
        LabelContentMust    内容过滤必须包含
        LabelContentForbid  内容过滤不得包含
        "length_filt_opertar": 0 不进行内容长度的过滤  1 大于 2 小于 3 等于 4 不等于,
		"length_filt_value": 0 需要过滤的字符串长度 如果为0 不过滤,
        如果需要过滤会返回true    否则返回false"""
    if not content:
        if LabelContentMust:
            # 传入的过滤原始数据为空 但又限制了必须包含 满足限制条件
            return True
        if LabelNotNull == 0:
            # 传入的内容为空 限制不能为空 满足限制条件
            return True

    if LabelContentForbid:
        '''检测是否进行不得包含过滤'''
        status = content_forbid(LabelContentForbid, content)
        if not status:
            # 返回false  即满足过滤条件
            # 直接返回继续
            return True
    if LabelContentMust:
        '''检测是否进行必须包含过滤'''
        status = content_must(LabelContentMust, content)
        if not status:
            # 返回false  即满足过滤条件
            # 直接返回继续
            return True
    if length_filt_opertar and length_filt_value:
        if isinstance(length_filt_opertar,int) and isinstance(length_filt_value,int):
            content_len = len(content)  # 检测网址长度
            if length_filt_opertar == 1:
                # 内容大于指定长度后过滤
                if content_len > length_filt_value:
                    return True
            elif length_filt_opertar == 2:
                # 内容小于指定长度后过滤
                if content_len < length_filt_value:
                    return True
            elif length_filt_opertar == 3:
                # 内容等于指定长度后过滤
                if content_len == length_filt_value:
                    return True
            elif length_filt_opertar == 4:
                # 内容不等于指定长度后过滤
                if content_len != length_filt_value:
                    return True


    return False


# 传入一个list  解析里面的<0,1,2,1,False,False>  如果存在解析好通过list返回  如果不存在直接返回原始数据
# 如果出现异常会返回 None
def locoy_parse_url_list(locoy_url_rule):
    '''传入列表或者字符串自动解析里面的网址并把解析的网址通过list返回'''
    ret_list = []
    if isinstance(locoy_url_rule, str):
        ret_list = locoy_parse_url(locoy_url_rule)
        return ret_list
    elif isinstance(locoy_url_rule, (list, tuple)):
        for temp_rule in locoy_url_rule:
            ret = locoy_parse_url(temp_rule)
            if ret:
                ret_list.extend(ret)
    else:
        return None
    return ret_list


def locoy_parse_url(locoy_url_rule):
    '''传入火车头的网址规则自动解析 生成一个list返回'''
    if not isinstance(locoy_url_rule, str):
        return None
    ret_rule_list = reg_parse_url.findall(locoy_url_rule)
    # http://www.hzzfcg.gov.cn/more.asp?classid=70&page=<0,1,2,1,False,False>#等差数列    第一个False补0   第二个 是否倒序
    # http://www.hzzfcg.gov.cn/more.asp?classid=70&page=<1,1,5,2,False,False>等比数列    第一个False补0   第二个 是否倒序
    # http://www.hzzfcg.gov.cn/more.asp?classid=70&page=<a,z,False>用字母替换
    if ret_rule_list:
        url_rule = ret_rule_list[0]
        temp_url_card_list = list()  # 临时存放等比 等差数列
        ret_list = list()  # 全部处理好的网址放到这个列表中 返回
        # 通过正则可以匹配出<  >中的5个参数  或者3个参数
        if url_rule[0] == '0':
            url_type = 0
            start_id = int(url_rule[1])
            num_id = int(url_rule[2])
            step_id = int(url_rule[3])
            temp_url_card_list = [
                start_id + n * step_id for n in range(num_id)
            ]
            # print(temp_url_card_list)
            # 表示等差数列
            pass
        elif url_rule[0] == '1':
            # 表示等比数列
            url_type = 1
            start_id = int(url_rule[1])
            num_id = int(url_rule[2])
            step_id = int(url_rule[3])
            temp_url_card_list = [start_id * step_id**n for n in range(num_id)]
            # print(temp_url_card_list)
        else:
            # 剩下的解析 字母变换  貌似没有用到  暂时不处理 遇到后再做处理
            url_type = 2
            pass
        if url_type == 2:
            # 表示是按照字母来的 目前没写直接返回
            return None
        # 将所有的数字转换成字符串
        temp_url_card_list = list(map(str, temp_url_card_list))
        if url_rule[4] == 'True':
            # 表示需要填充0
            # 首先计算字符的最长长度
            max_len = len(temp_url_card_list[-1])
            for nn in range(len(temp_url_card_list)):
                if len(temp_url_card_list[nn]) < max_len:
                    # 长度不够尽兴补0处理
                    temp_url_card_list[nn] = ''.join(
                        ('0' * (max_len - len(temp_url_card_list[nn])),
                         temp_url_card_list[nn]))
                else:
                    break
        if url_rule[5] == 'True':
            # 表示倒序处理
            temp_url_card_list.reverse()

        for text in temp_url_card_list:
            new_url = reg_parse_url.sub(text, locoy_url_rule)
            ret_list.append(new_url)
        return ret_list
    temp_list = list(
    )  # 因为返回的必须是列表  传入的是字符串 如果运行到这表示上面代码没有执行  把传入的网址直接加到list中返回
    temp_list.append(locoy_url_rule)
    return temp_list


##########火车头规则解析   结束#########


# 返回一个时间文本 返回格式 2016-12-12 13:12:43
def get_time_str():
    '''回去一个时间文本 返回格式 2016-12-12 13:12:43'''
    return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(time.time()))


# 获取一个时间戳 返回str
def get_timestamp(str_len=13):
    """返回一个时间戳    默认返回13位的 如果要返回10位的  传入10即可"""

    for n in range(20):
        time_str = time.time()
        if time_str > 1482302688:
            # 表示生成时间戳 正确  否则可以获取失败 重新进行获取
            break
    if str_len == 13:
        return str(int(time_str * 1000))
    else:
        return str(int(time_str))


# 传入一个时间戳转化为 '%Y-%m-%d %H:%M:%S' 格式的时间
def timestamp_to_date(timestamp):
    # 时间戳 可以传入int  str 两种类型
    # 传入一个时间戳转化为 '%Y-%m-%d %H:%M:%S' 格式的时间
    try:
        if type(timestamp) in [int]:
            if timestamp > 10000000000:
                temp_str = str(timestamp)[0:10]
                temp_timestamp = int(temp_str)
            elif timestamp < 1000000000:
                # 小于9位不符合
                return ''
            else:
                temp_timestamp = timestamp
        elif type(timestamp) in [str, str]:
            if len(timestamp) < 10:
                # 长度小于10的时间戳无法转换
                return ''
            temp_str = timestamp[0:10]
            temp_timestamp = int(temp_str)
        else:
            return ''
        time_str = time.strftime("%Y-%m-%d %H:%M:%S",
                                 time.gmtime(temp_timestamp))
    except BaseException:
        return ''
    return time_str


# 设置一个开机启动
def start_run(run_parh, eun_name):
    '''设置启动的时候运行指定的程序   目前只测试了win xp
    run_path  为所需要运行的软件所在的目录
    run_name 为要运行的软件的名字
    '''

    try:
        tt = r'''cd {}
        {}'''.format(run_parh, eun_name)
        tt = tt.decode("utf-8").encode("gb2312")
        write_log(r'C:\Documents and Settings\All Users\「开始」菜单\程序\启动\run.bat',
                  tt, 'w')
    except BaseException:
        return False
    return True


# 删除一个开机启动
def delete_start():
    try:
        filename = r'C:\Documents and Settings\All Users\「开始」菜单\程序\启动\run.bat'
        if os.path.exist(filename):
            os.remove(filename)
    except BaseException:
        return False
    return True


# 写文件 传入路径 写出内容  默认为追加模式
def write_log(path, text, mode='a'):
    '''默认为追加模式'''
    with open(path, mode) as loger_log:
        loger_log.write(('%s\n' % text))


def Network_connection():
    '''通过访问百度 判断当前网络是否联网  如果可以访问返回True   否则返回False'''
    url = 'http://www.baidu.com'
    for x in range(2):
        try:
            # , allow_redirects=False  禁止重定向
            r = requests.get(url, timeout=3, allow_redirects=False)
            error = ''
            break
        except Exception as error:
            pass
    if error == '':
        code = r.status_code
        if code == 302 or code == 200:
            return True
    return False


# print get_str_mid("1234asds56789542343152","2","5" )
# print(sys.version)
#print(get_str_mid_wildcard("12345dfdf4fghfh6456fgfjhgiui6789yrtuyfeyu67890", "45", "6789" ,find_order=False))
# print timestamp_to_date('14861220580')
# print(get_str_mid_reg(text,'msgList\s?=',";\s",escape=False))
def quote_chinese(url, encodeing="utf-8", errors='replace'):
    """Quote non-ascii characters"""
    if isinstance(url, six.text_type):
        return quote_chinese(url.encode(encodeing, errors=errors))
    if six.PY3:
        res = [
            six.int2byte(b).decode('latin-1', errors=errors) if b < 128 else '%%%02X' % b
            for b in url
        ]
    else:
        res = [b if ord(b) < 128 else '%%%02X' % ord(b) for b in url]
    return "".join(res)


if __name__ == '__main__':
    print(check_time('2017-06-1'))
    pass
