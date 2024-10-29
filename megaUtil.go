package main

import (
	"bufio"
	"bytes"
	"compress/flate"
	"compress/gzip"
	"crypto/aes"
	"crypto/cipher"
	"crypto/md5"
	crand "crypto/rand"
	"crypto/sha1"
	"crypto/sha256"
	"crypto/sha512"
	"crypto/tls"
	"database/sql"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"html/template"
	"io"
	"math"
	"math/rand"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode"
	"unicode/utf8"
	"unsafe"

	"github.com/PuerkitoBio/goquery"
	"github.com/gin-contrib/cors"
	"github.com/gin-gonic/gin"
	"github.com/xuri/excelize/v2"
	"golang.org/x/text/encoding/ianaindex"
	"golang.org/x/text/transform"
)

const (
	HttpDefaultTimeOut        = 10000
	HttpDefaultUserAgent      = "Mozilla/5.0 (Windows NT 6.1; WOW64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/114.0.0.0 Safari/537.36"
	HttpDefaultAcceptEncoding = "gzip, deflate"
)

type HttpReq struct {
	// UserAgent 优先于请求头 Headers 中的 User-Agent 字段
	UserAgent string

	// 请求头
	Headers map[string]string

	// 限制最大返回大小
	MaxContentLength int64

	// 限制允许访问 ContentType 列表, 前缀匹配
	AllowedContentTypes []string

	// 最大 Redirect 次数, 范围 [0,10), 否则采用默认的跳转策略 (最大限制 10 次)
	MaxRedirect int

	// 禁止跳转
	DisableRedirect bool

	// 请求失败错误时仍然读取 Body
	ReadBodyWithFail bool

	// http.Transport
	Transport http.RoundTripper

	// http.CookieJar
	Jar http.CookieJar
}

type HttpResp struct {
	// 是否成功 (200-299), 成功仍可能返回 err
	Success bool

	// Http 状态码
	StatusCode int

	// 响应体
	Body []byte

	// ContentLength (字节数)
	ContentLength int64

	// 响应头
	Headers *http.Header

	// 最后请求
	RequestURL *url.URL
}

// HttpDefaultTransport 默认全局使用的 http.Transport
var HttpDefaultTransport = &http.Transport{
	DialContext:           (&net.Dialer{Timeout: time.Second}).DialContext,
	ForceAttemptHTTP2:     true,
	MaxIdleConns:          150,
	MaxIdleConnsPerHost:   3,
	IdleConnTimeout:       60 * time.Second,
	TLSHandshakeTimeout:   10 * time.Second,
	ExpectContinueTimeout: 1 * time.Second,
	TLSClientConfig:       &tls.Config{InsecureSkipVerify: true},
}

// HttpGet 参数为请求地址 (HttpReq, 超时时间)
// HttpGet(url)、HttpGet(url, HttpReq)、HttpGet(url, timeout)、HttpGet(url, HttpReq, timeout)
// 返回 body, 错误信息
// export
func HttpGet(urlStr string, args ...any) ([]byte, error) {
	l := len(args)

	switch l {
	case 0:
		return HttpGetDo(urlStr, nil, 0)
	case 1:
		switch v := args[0].(type) {
		case int:
			timeout := ToInt(args[0])
			return HttpGetDo(urlStr, nil, timeout)
		case *HttpReq:
			return HttpGetDo(urlStr, v, 0)
		}
	case 2:
		timeout := ToInt(args[1])
		switch v := args[0].(type) {
		case *HttpReq:
			return HttpGetDo(urlStr, v, timeout)
		}
	}

	return nil, errors.New("http get params error")
}

// HttpDelete 参数为请求地址 (HttpReq, 超时时间)
// HttpDelete(url)、HttpDelete(url, HttpReq)、HttpDelete(url, timeout)、HttpDelete(url, HttpReq, timeout)
// 返回 body, 错误信息
// export
func HttpDelete(urlStr string, args ...any) ([]byte, error) {
	l := len(args)

	switch l {
	case 0:
		return HttpDeleteDo(urlStr, nil, 0)
	case 1:
		switch v := args[0].(type) {
		case int:
			timeout := ToInt(args[0])
			return HttpDeleteDo(urlStr, nil, timeout)
		case *HttpReq:
			return HttpDeleteDo(urlStr, v, 0)
		}
	case 2:
		timeout := ToInt(args[1])
		switch v := args[0].(type) {
		case *HttpReq:
			return HttpDeleteDo(urlStr, v, timeout)
		}
	}

	return nil, errors.New("http delete params error")
}

// HttpPost 参数为请求地址 (body io.Reader, HttpReq, 超时时间)
// HttpPost(url)、HttpPost(url, timeout)、HttpPost(url, body)、HttpPost(url, body, timeout)、HttpPost(url, body, HttpReq)、HttpPostForm(url, body, HttpReq, timeout)
// 返回 body, 错误信息
// export
func HttpPost(urlStr string, args ...any) ([]byte, error) {
	l := len(args)

	switch l {
	case 0:
		return HttpPostDo(urlStr, nil, nil, 0)
	case 1:
		switch v := args[0].(type) {
		case int:
			timeout := ToInt(args[0])
			return HttpPostDo(urlStr, nil, nil, timeout)
		case io.Reader:
			return HttpPostDo(urlStr, v, nil, 0)
		}
	case 2:
		switch v := args[0].(type) {
		case io.Reader:
			switch h := args[1].(type) {
			case int:
				timeout := ToInt(args[1])
				return HttpPostDo(urlStr, v, nil, timeout)
			case *HttpReq:
				return HttpPostDo(urlStr, v, h, 0)
			}
		}
	case 3:
		switch v := args[0].(type) {
		case io.Reader:
			switch h := args[1].(type) {
			case *HttpReq:
				timeout := ToInt(args[2])
				return HttpPostDo(urlStr, v, h, timeout)
			}
		}
	}

	return nil, errors.New("http post params error")
}

// HttpPut 参数为请求地址 (body io.Reader, HttpReq, 超时时间)
// HttpPut(url)、HttpPut(url, timeout)、HttpPut(url, body)、HttpPut(url, body, timeout)、HttpPut(url, body, HttpReq)、HttpPut(url, body, HttpReq, timeout)
// 返回 body, 错误信息
// export
func HttpPut(urlStr string, args ...any) ([]byte, error) {
	l := len(args)

	switch l {
	case 0:
		return HttpPutDo(urlStr, nil, nil, 0)
	case 1:
		switch v := args[0].(type) {
		case int:
			timeout := ToInt(args[0])
			return HttpPutDo(urlStr, nil, nil, timeout)
		case io.Reader:
			return HttpPutDo(urlStr, v, nil, 0)
		}
	case 2:
		switch v := args[0].(type) {
		case io.Reader:
			switch h := args[1].(type) {
			case int:
				timeout := ToInt(args[1])
				return HttpPutDo(urlStr, v, nil, timeout)
			case *HttpReq:
				return HttpPutDo(urlStr, v, h, 0)
			}
		}
	case 3:
		switch v := args[0].(type) {
		case io.Reader:
			switch h := args[1].(type) {
			case *HttpReq:
				timeout := ToInt(args[2])
				return HttpPutDo(urlStr, v, h, timeout)
			}
		}
	}

	return nil, errors.New("http post params error")
}

// HttpPutForm 参数为请求地址 (Form 数据 map[string]string, HttpReq, 超时时间)
// HttpPutForm(url)、HttpPutForm(url, timeout)、HttpPutForm(url, posts)、HttpPutForm(url, posts, timeout)、HttpPutForm(url, posts, HttpReq)、HttpPutForm(url, posts, HttpReq, timeout)
// 返回 body, 错误信息
// export
func HttpPutForm(urlStr string, args ...any) ([]byte, error) {
	l := len(args)

	switch l {
	case 0:
		return HttpPutFormDo(urlStr, nil, nil, 0)
	case 1:
		switch v := args[0].(type) {
		case int:
			timeout := ToInt(args[0])
			return HttpPutFormDo(urlStr, nil, nil, timeout)
		case map[string]string:
			return HttpPutFormDo(urlStr, v, nil, 0)
		}
	case 2:
		switch v := args[0].(type) {
		case map[string]string:
			switch h := args[1].(type) {
			case int:
				timeout := ToInt(args[1])
				return HttpPutFormDo(urlStr, v, nil, timeout)
			case *HttpReq:
				return HttpPutFormDo(urlStr, v, h, 0)
			}
		}
	case 3:
		switch v := args[0].(type) {
		case map[string]string:
			switch h := args[1].(type) {
			case *HttpReq:
				timeout := ToInt(args[2])
				return HttpPutFormDo(urlStr, v, h, timeout)
			}
		}
	}

	return nil, errors.New("http post form params error")
}

// HttpPutJson 参数为请求地址 (Json 数据 string, HttpReq, 超时时间)
// HttpPutJson(url)、HttpPutJson(url, timeout)、HttpPutJson(url, json)、HttpPutJson(url, json, timeout)、HttpPutJson(url, json, httpReq)、HttpPutJson(url, json, httpReq, timeout)
// 返回 body, 错误信息
// export
func HttpPutJson(urlStr string, args ...any) ([]byte, error) {
	l := len(args)
	switch l {
	case 0:
		return HttpPutJsonDo(urlStr, "{}", nil, 0)
	case 1:
		switch v := args[0].(type) {
		case int:
			timeout := ToInt(args[0])
			return HttpPutJsonDo(urlStr, "{}", nil, timeout)
		case string:
			return HttpPutJsonDo(urlStr, v, nil, 0)
		}
	case 2:
		switch v := args[0].(type) {
		case string:
			switch h := args[1].(type) {
			case int:
				timeout := ToInt(args[1])
				return HttpPutJsonDo(urlStr, v, nil, timeout)
			case *HttpReq:
				return HttpPutJsonDo(urlStr, v, h, 0)
			}
		}
	case 3:
		switch v := args[0].(type) {
		case string:
			switch h := args[1].(type) {
			case *HttpReq:
				timeout := ToInt(args[2])
				return HttpPutJsonDo(urlStr, v, h, timeout)
			}
		}
	}

	return nil, errors.New("http post json params error")
}

// HttpGetDo Http Get 请求, 参数为请求地址, HttpReq, 超时时间(毫秒)
// 返回 body, 错误信息
// export
func HttpGetDo(urlStr string, r *HttpReq, timeout int) ([]byte, error) {
	resp, err := HttpGetResp(urlStr, r, timeout)
	if err != nil {
		return resp.Body, err
	} else {
		return resp.Body, nil
	}
}

// HttpDeleteDo Http Delete 请求, 参数为请求地址, HttpReq, 超时时间(毫秒)
// 返回 body, 错误信息
// export
func HttpDeleteDo(urlStr string, r *HttpReq, timeout int) ([]byte, error) {
	resp, err := HttpDeleteResp(urlStr, r, timeout)
	if err != nil {
		return resp.Body, err
	} else {
		return resp.Body, nil
	}
}

// HttpPostDo Http Post, 参数为请求地址, body io.Reader, HttpReq, 超时时间(毫秒)
// 返回 body, 错误信息
// export
func HttpPostDo(urlStr string, body io.Reader, r *HttpReq, timeout int) ([]byte, error) {
	resp, err := HttpPostResp(urlStr, body, r, timeout)
	if err != nil {
		return resp.Body, err
	} else {
		return resp.Body, nil
	}
}

// HttpPostFormDo Http Post Form, 参数为请求地址, Form 数据 map[string]string, HttpReq, 超时时间(毫秒)
// 返回 body, 错误信息
// export
func HttpPostFormDo(urlStr string, posts map[string]string, r *HttpReq, timeout int) ([]byte, error) {
	resp, err := HttpPostFormResp(urlStr, posts, r, timeout)
	if err != nil {
		return resp.Body, err
	} else {
		return resp.Body, nil
	}
}

// HttpPostJsonDo Http Post Json 请求, 参数为请求地址, Json 数据 string, HttpReq, 超时时间(毫秒)
// 返回 body, 错误信息
// export
func HttpPostJsonDo(urlStr string, json string, r *HttpReq, timeout int) ([]byte, error) {
	resp, err := HttpPostJsonResp(urlStr, json, r, timeout)
	if err != nil {
		return resp.Body, err
	} else {
		return resp.Body, nil
	}
}

// HttpPutDo Http Put, 参数为请求地址, body io.Reader, HttpReq, 超时时间(毫秒)
// 返回 body, 错误信息
// export
func HttpPutDo(urlStr string, body io.Reader, r *HttpReq, timeout int) ([]byte, error) {
	resp, err := HttpPutResp(urlStr, body, r, timeout)
	if err != nil {
		return resp.Body, err
	} else {
		return resp.Body, nil
	}
}

// HttpPutFormDo Http Put Form, 参数为请求地址, Form 数据 map[string]string, HttpReq, 超时时间(毫秒)
// 返回 body, 错误信息
// export
func HttpPutFormDo(urlStr string, posts map[string]string, r *HttpReq, timeout int) ([]byte, error) {
	resp, err := HttpPutFormResp(urlStr, posts, r, timeout)
	if err != nil {
		return resp.Body, err
	} else {
		return resp.Body, nil
	}
}

// HttpPutJsonDo Http Put Json 请求, 参数为请求地址, Json 数据 string, HttpReq, 超时时间(毫秒)
// 返回 body, 错误信息
// export
func HttpPutJsonDo(urlStr string, json string, r *HttpReq, timeout int) ([]byte, error) {
	resp, err := HttpPutJsonResp(urlStr, json, r, timeout)
	if err != nil {
		return resp.Body, err
	} else {
		return resp.Body, nil
	}
}

// HttpGetResp Http Get 请求, 参数为请求地址, HttpReq, 超时时间(毫秒)
// 返回 HttpResp, 错误信息
// export
func HttpGetResp(urlStr string, r *HttpReq, timeout int) (*HttpResp, error) {
	req, err := http.NewRequest(http.MethodGet, urlStr, nil)
	if err != nil {
		return nil, err
	}

	return HttpDoResp(req, r, timeout)
}

// HttpDeleteResp Http Delete 请求, 参数为请求地址, HttpReq, 超时时间(毫秒)
// 返回 HttpResp, 错误信息
// export
func HttpDeleteResp(urlStr string, r *HttpReq, timeout int) (*HttpResp, error) {
	req, err := http.NewRequest(http.MethodDelete, urlStr, nil)
	if err != nil {
		return nil, err
	}

	return HttpDoResp(req, r, timeout)
}

// HttpPostResp Http Post, 参数为请求地址, body io.Reader, HttpReq, 超时时间(毫秒)
// 返回 HttpResp, 错误信息
// export
func HttpPostResp(urlStr string, body io.Reader, r *HttpReq, timeout int) (*HttpResp, error) {
	req, err := http.NewRequest(http.MethodPost, urlStr, body)
	if err != nil {
		return nil, err
	}

	return HttpDoResp(req, r, timeout)
}

// HttpPostFormResp Http Post Form, 参数为请求地址, Form 数据 map[string]string, HttpReq, 超时时间(毫秒)
// 返回 HttpResp, 错误信息
// export
func HttpPostFormResp(urlStr string, posts map[string]string, r *HttpReq, timeout int) (*HttpResp, error) {
	data := url.Values{}
	if len(posts) > 0 {
		for k, v := range posts {
			data.Set(k, v)
		}
	}

	req, err := http.NewRequest(http.MethodPost, urlStr, strings.NewReader(data.Encode()))
	if err != nil {
		return nil, err
	}

	req.Header.Set("Content-Type", MimePostForm)

	return HttpDoResp(req, r, timeout)
}

// HttpPostJsonResp Http Post Json 请求, 参数为请求地址, Json 数据 string, HttpReq, 超时时间(毫秒)
// 返回 HttpResp, 错误信息
// export
func HttpPostJsonResp(urlStr string, json string, r *HttpReq, timeout int) (*HttpResp, error) {
	req, err := http.NewRequest(http.MethodPost, urlStr, strings.NewReader(json))
	if err != nil {
		return nil, err
	}

	req.Header.Set("Content-Type", MimeJson)

	return HttpDoResp(req, r, timeout)
}

// HttpPutResp Http Put, 参数为请求地址, body io.Reader, HttpReq, 超时时间(毫秒)
// 返回 HttpResp, 错误信息
// export
func HttpPutResp(urlStr string, body io.Reader, r *HttpReq, timeout int) (*HttpResp, error) {
	req, err := http.NewRequest(http.MethodPut, urlStr, body)
	if err != nil {
		return nil, err
	}

	return HttpDoResp(req, r, timeout)
}

// HttpPutFormResp Http Put Form, 参数为请求地址, Form 数据 map[string]string, HttpReq, 超时时间(毫秒)
// 返回 HttpResp, 错误信息
// export
func HttpPutFormResp(urlStr string, posts map[string]string, r *HttpReq, timeout int) (*HttpResp, error) {
	data := url.Values{}
	if len(posts) > 0 {
		for k, v := range posts {
			data.Set(k, v)
		}
	}

	req, err := http.NewRequest(http.MethodPut, urlStr, strings.NewReader(data.Encode()))
	if err != nil {
		return nil, err
	}

	req.Header.Set("Content-Type", MimePostForm)

	return HttpDoResp(req, r, timeout)
}

// HttpPutJsonResp Http Put Json 请求, 参数为请求地址, Json 数据 string, HttpReq, 超时时间(毫秒)
// 返回 HttpResp, 错误信息
// export
func HttpPutJsonResp(urlStr string, json string, r *HttpReq, timeout int) (*HttpResp, error) {
	req, err := http.NewRequest(http.MethodPut, urlStr, strings.NewReader(json))
	if err != nil {
		return nil, err
	}

	req.Header.Set("Content-Type", MimeJson)

	return HttpDoResp(req, r, timeout)
}

// HttpDo Http 请求, 参数为 http.Request, HttpReq, 超时时间(毫秒)
// 返回 body, 错误信息
// export
func HttpDo(req *http.Request, r *HttpReq, timeout int) ([]byte, error) {
	resp, err := HttpDoResp(req, r, timeout)
	if err != nil {
		return resp.Body, err
	} else {
		return resp.Body, nil
	}
}

// HttpDoResp Http 请求, 参数为 http.Request, HttpReq, 超时时间(毫秒)
// 返回 HttpResp, 错误信息
// export
func HttpDoResp(req *http.Request, r *HttpReq, timeout int) (*HttpResp, error) {
	if timeout == 0 {
		timeout = HttpDefaultTimeOut
	}

	// NewClient
	var client *http.Client
	if r != nil && r.Transport != nil {
		client = &http.Client{
			Timeout:   time.Duration(timeout) * time.Millisecond,
			Transport: r.Transport,
			Jar:       r.Jar,
		}
	} else {
		client = &http.Client{
			Timeout:   time.Duration(timeout) * time.Millisecond,
			Transport: HttpDefaultTransport,
		}
	}

	// Redirect 策略
	if r == nil || r.DisableRedirect {
		client.CheckRedirect = func(req *http.Request, via []*http.Request) error {
			return http.ErrUseLastResponse
		}
	} else if r.MaxRedirect > 0 && r.MaxRedirect < 10 {
		client.CheckRedirect = func(req *http.Request, via []*http.Request) error {
			if len(via) > r.MaxRedirect {
				return http.ErrUseLastResponse
			}
			return nil
		}
	}

	// 处理请求头
	headers := make(map[string]string)
	if r != nil && r.UserAgent != "" {
		r.Headers["User-Agent"] = r.UserAgent
	}
	if r != nil && r.Headers != nil && len(r.Headers) > 0 {
		headers = r.Headers
		if _, exist := headers["User-Agent"]; !exist {
			headers["User-Agent"] = HttpDefaultUserAgent
		}
		if _, exist := headers["Accept-Encoding"]; !exist {
			headers["Accept-Encoding"] = HttpDefaultAcceptEncoding
		}
	} else {
		headers["User-Agent"] = HttpDefaultUserAgent
		headers["Accept-Encoding"] = HttpDefaultAcceptEncoding
	}
	for k, v := range headers {
		req.Header.Set(k, v)
	}

	// HttpResp
	httpResp := &HttpResp{}
	var body []byte
	httpResp.Body = body

	// Do
	resp, err := client.Do(req)
	if err != nil {
		return httpResp, errors.New("ErrorDo")
	}
	defer resp.Body.Close()

	// 响应
	httpResp.StatusCode = resp.StatusCode
	if resp.StatusCode >= 200 && resp.StatusCode < 300 {
		httpResp.Success = true
	} else {
		if !r.ReadBodyWithFail {
			return httpResp, errors.New("ErrorStatusCode")
		}
	}

	httpResp.Headers = &resp.Header
	httpResp.ContentLength = resp.ContentLength
	httpResp.RequestURL = resp.Request.URL

	// http.Transport 定义了当请求头不包含 Accept-Encoding 或为空时, 默认会发送 Accept-Encoding=gzip
	// 它会自动判断服务端是否是gzip 然后在接受响应时自动 uncompress, 并会自动移除响应头中的 Content-Encoding、Content-Length
	// 为了获取 Content-Length, 我们需要手动设置不为空的 Accept-Encoding (默认是 HttpDefaultAcceptEncoding), 并且手动 uncompress
	var reader io.ReadCloser
	switch strings.ToLower(resp.Header.Get("Content-Encoding")) {
	case "gzip":
		reader, err = gzip.NewReader(resp.Body)
		if err != nil {
			return httpResp, errors.New("ErrorGzip")
		}
	case "deflate":
		reader = flate.NewReader(resp.Body)
	default:
		reader = resp.Body
	}
	defer reader.Close()

	// ContentType 限制
	if _, err := allowContentTypes(r, httpResp.Headers); err != nil {
		return httpResp, err
	}

	// ContentLength 限制
	if r != nil && r.MaxContentLength > 0 {
		if resp.ContentLength != -1 {
			if resp.ContentLength > r.MaxContentLength {
				return httpResp, errors.New("ErrorContentLength")
			}
			body, err = io.ReadAll(reader)
		} else {
			// 只读取到最大长度, 就立即返回, 根据读取到的数据判断是否返回错误
			body, err = io.ReadAll(io.LimitReader(reader, r.MaxContentLength))
			bodyLen := int64(len(body))
			if bodyLen < r.MaxContentLength {
				httpResp.Body = body
			} else {
				return httpResp, errors.New("ErrorContentLength")
			}
		}
	} else {
		body, err = io.ReadAll(reader)
	}

	if err != nil {
		return httpResp, errors.New("ErrorReadBody")
	} else {
		httpResp.Body = body
	}

	if httpResp.Success {
		return httpResp, nil
	} else {
		return httpResp, errors.New("ErrorStatusCode")
	}
}

// allowContentTypes 判断 Content-Type 是否在允许列表中
// export
func allowContentTypes(r *HttpReq, headers *http.Header) (bool, error) {
	if r == nil {
		return true, nil
	}

	if len(r.AllowedContentTypes) > 0 {
		valid := false

		ct := strings.TrimSpace(strings.ToLower(headers.Get("Content-Type")))
		for _, t := range r.AllowedContentTypes {
			if strings.HasPrefix(ct, t) {
				valid = true
				break
			}
		}

		if valid {
			return valid, nil
		} else {
			return valid, errors.New("ErrorContentType")
		}
	}

	return true, nil
}

// UrlParse url.Parse 在没有 scheme 时不会出错
// export
func UrlParse(rawURL string) (*url.URL, error) {
	u, err := url.Parse(rawURL)
	if err == nil {
		if u.Hostname() != "" {
			return u, nil
		} else {
			return nil, errors.New("url hostname is empty")
		}
	} else {
		return nil, errors.New("url parse error")
	}
}

// export
func PostRequest(urlStr string, data map[string]interface{}) (map[string]interface{}, error) {
	// Convertir los datos a JSON
	jsonData, err := json.Marshal(data)
	if err != nil {
		return nil, err
	}

	// Hacer el request POST
	resp, err := http.Post(urlStr, "application/json", bytes.NewBuffer(jsonData))
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	// Decodificar la respuesta JSON
	var result map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, err
	}

	return result, nil
}

// PostRequestForm realiza un request POST a la URL especificada con datos URL-encoded.
// export
func PostRequestForm(urlStr string, data map[string]interface{}) (map[string]interface{}, error) {
	// Codificar los datos en formato URL-encoded
	form := url.Values{}
	for key, value := range data {
		form.Set(key, formatValue(value))
	}

	// Hacer el request POST
	resp, err := http.Post(urlStr, "application/x-www-form-urlencoded", bytes.NewBufferString(form.Encode()))
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	// Decodificar la respuesta JSON
	var result map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, err
	}

	return result, nil
}

// GetRequest realiza un request GET a la URL especificada con parámetros en la query.
// export
func GetRequest(baseUrl string, params map[string]interface{}) (map[string]interface{}, error) {
	// Construir la URL con parámetros
	query := url.Values{}
	for key, value := range params {
		query.Set(key, formatValue(value))
	}

	// Crear la URL completa
	fullUrl := baseUrl + "?" + query.Encode()

	// Hacer el request GET
	resp, err := http.Get(fullUrl)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	// Decodificar la respuesta JSON
	var result map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, err
	}

	return result, nil
}

// export
func PostRequestRawForm(urlStr string, data map[string]interface{}) (string, error) {
	// Codificar los datos en formato URL-encoded
	form := url.Values{}
	for key, value := range data {
		form.Set(key, formatValue(value))
	}

	// Hacer el request POST
	resp, err := http.Post(urlStr, "application/x-www-form-urlencoded", bytes.NewBufferString(form.Encode()))
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()

	// Leer el cuerpo de la respuesta
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}

	return string(body), nil
}

// export
func PostRequestRaw(urlStr string, data map[string]interface{}) (string, error) {
	// Convertir los datos a JSON
	jsonData, err := json.Marshal(data)
	if err != nil {
		return "", err
	}

	// Hacer el request POST
	resp, err := http.Post(urlStr, "application/json", bytes.NewBuffer(jsonData))
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()

	// Leer el cuerpo de la respuesta
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}

	return string(body), nil
}

// formatValue convierte un valor de interface{} a string.
// export
func formatValue(value interface{}) string {
	switch v := value.(type) {
	case string:
		return v
	case int, int32, int64:
		return fmt.Sprintf("%d", v)
	case float32, float64:
		return fmt.Sprintf("%f", v)
	case bool:
		return fmt.Sprintf("%t", v)
	default:
		return ""
	}
}

// export
func Hoy() string {
	return time.Now().Format("2006-01-02")
}

// export
func DateTime() string {
	return time.Now().Format("2006-01-02 15:04:05") // Formato de Go
}

// export
func UnixTime() int64 {
	return time.Now().Unix() // Devuelve el tiempo en segundos desde epoch
}

// export
func UnixMillisecTime() int64 {
	return time.Now().UnixNano() / int64(time.Millisecond) // Devuelve el tiempo en milisegundos desde epoch
}

// export
func DiaHoy() string {
	fechaActual := time.Now()
	nombreDia := fechaActual.Weekday().String()

	diasSemana := map[string]string{
		"Monday":    "Lunes",
		"Tuesday":   "Martes",
		"Wednesday": "Miércoles",
		"Thursday":  "Jueves",
		"Friday":    "Viernes",
		"Saturday":  "Sábado",
		"Sunday":    "Domingo",
	}

	return diasSemana[nombreDia]
}

// AesCBCEncrypt Aes CBC 对称加密, key 的长度决定 AES-128, AES-192, or AES-256
// export
func AesCBCEncrypt(text string, key string, iv string) (string, error) {
	textBytes := Bytes(text)
	keyBytes := Bytes(key)
	ivBytes := Bytes(iv)

	block, err := aes.NewCipher(keyBytes)
	if err != nil {
		return "", errors.New(err.Error())
	}

	// 对数据进行填充，使其满足加密块大小，加密块大小为 16 字节
	blockSize := block.BlockSize()
	paddingText := pKCS7Padding(textBytes, blockSize)

	// 创建加密块链，使用 CBC 加密模式，iv 的长度需要和 block.BlockSize() 一致
	mode := cipher.NewCBCEncrypter(block, ivBytes)

	// 加密数据
	cipherText := make([]byte, len(paddingText))
	mode.CryptBlocks(cipherText, paddingText)
	cipherHex := hex.EncodeToString(cipherText)

	return cipherHex, nil
}

// AesCBCDecrypt Aes CBC 对称加密
// export
func AesCBCDecrypt(cipherStr string, key string, iv string) (string, error) {
	cipherBytes, err := hex.DecodeString(cipherStr)
	if err != nil {
		return "", errors.New(err.Error())
	}

	keyBytes := Bytes(key)
	ivBytes := Bytes(iv)

	// 创建解密器
	block, err := aes.NewCipher(keyBytes)
	if err != nil {
		return "", errors.New(err.Error())
	}

	// 创建解密块链
	mode := cipher.NewCBCDecrypter(block, ivBytes)

	// 解密数据
	textBytes := make([]byte, len(cipherBytes))
	mode.CryptBlocks(textBytes, cipherBytes)

	textBytes = pKCS7UnPadding(textBytes)

	return String(textBytes), nil
}

// pKCS7Padding 对数据进行填充，满足加密块大小
// export
func pKCS7Padding(data []byte, blockSize int) []byte {
	padding := blockSize - len(data)%blockSize
	padText := bytes.Repeat([]byte{byte(padding)}, padding)

	return append(data, padText...)
}

// pKCS7UnPadding 去除填充的数据
// export
func pKCS7UnPadding(data []byte) []byte {
	length := len(data)
	unPadding := int(data[length-1])

	return data[:(length - unPadding)]
}

const (
	SPACE      = " "
	DOT        = "."
	SLASH      = "/"
	UNDERSCORE = "_"
	COLON      = ":"
	DASH       = "-"
	LF         = "\n"
	CRLF       = "\r\n"
	CR         = "\r"
	TAB        = "\t"
)

const (
	DatePattern               = "2006-01-02"
	DatePatternSlash          = "2006/01/02"
	DatePatternUnderscore     = "2006_01_02"
	DatePatternZh             = "2006年01月02日"
	DatetimePattern           = "2006-01-02 15:04:05"
	DatetimeMilliPattern      = "2006-01-02 15:04:05.999"
	DatetimePatternSlash      = "2006/01/02 15:04:05"
	DatetimeMilliPatternSlash = "2006/01/02 15:04:05.999"
	DatetimePatternZh         = "2006年01月02日 15时04分05秒"
	DatetimePatternUtc        = "2006-01-02'T'15:04:05'Z'"
)

const (
	StringNumber          = "0123456789"
	StringUpperLetter     = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
	StringLowerLetter     = "abcdefghijklmnopqrstuvwxyz"
	StringLetter          = StringUpperLetter + StringLowerLetter
	StringLetterAndNumber = StringLetter + StringNumber
)

const (
	MimePlain             = "text/plain"
	MimeHtml              = "text/html"
	MimeJson              = "application/json"
	MimePostForm          = "application/x-www-form-urlencoded"
	MimeMultipartPostForm = "multipart/form-data"
	MimeProtobuf          = "application/x-protobuf"
	MimeYaml              = "application/x-yaml"
)

const (
	SizeB  = "B"
	SizeKB = "KB"
	SizeMB = "MB"
	SizeGB = "GB"
	SizeTB = "TB"
	SizePB = "PB"
	SizeEB = "EB"
)

const (
	_ = 1 << (10 * iota)
	BytesPerKB
	BytesPerMB
	BytesPerGB
	BytesPerTB
	BytesPerPB
	BytesPerEB
)

// export
func Timestamp(millis ...any) int64 {
	l := len(millis)
	switch l {
	case 0:
		return unixTimestamp()
	case 1:
		switch v := millis[0].(type) {
		case bool:
			if v {
				return unixMilliTimestamp()
			}
		}
	}

	return unixTimestamp()
}

// unixTimestamp 返回当前时间的 Unix 秒级时间戳
// export
func unixTimestamp() int64 {
	return time.Now().Unix()
}

// unixMilliTimestamp 返回当前时间的 Unix 毫秒级时间戳
// export
func unixMilliTimestamp() int64 {
	return time.Now().UnixMilli()
}

// Date 返回格式化后的日期时间字符串。
// 支持 Date()、Date(unixStamp)、Date(layout)、Date(layout, unixStamp)
// export
func Date(layouts ...any) string {
	l := len(layouts)

	switch l {
	case 0:
		return dateByDefault()
	case 1:
		switch v := layouts[0].(type) {
		case string:
			return dateByPattern(ToString(v))
		case int, int8, int16, int32, int64:
			return dateByPatternAndTime("", ToInt64(v))
		}
	case 2:
		switch layouts[0].(type) {
		case string:
			switch v := layouts[1].(type) {
			case int, int8, int16, int32, int64:
				return dateByPatternAndTime(ToString(layouts[0]), ToInt64(v))
			}
		}
	}

	return ""
}

// dateByDefault 返回默认 layout 格式化后的日期时间字符串
// export
func dateByDefault() string {
	now := time.Now()
	return now.Format(DatetimePattern)
}

// dateByPattern 返回指定 layout 格式化后的日期时间字符串
// export
func dateByPattern(layout string) string {
	now := time.Now()

	if Blank(layout) {
		return now.Format(DatetimePattern)
	} else {
		return now.Format(layout)
	}
}

// dateByPatternAndTime 返回指定时间戳、指定 layout 格式化后的日期时间字符串
// export
func dateByPatternAndTime(layout string, timeStamp int64) string {
	if timeStamp < 0 {
		timeStamp = 0
	}
	uTime := time.Unix(timeStamp, 0)

	if Blank(layout) {
		return uTime.Format(DatetimePattern)
	} else {
		return uTime.Format(layout)
	}
}

// StrToTime 日期时间字符串转时间戳
// 支持 StrToTime()、StrToTime(string)、StrToTime(string, int64)
// export
func StrToTime(args ...any) int64 {
	l := len(args)

	switch l {
	case 0:
		return Timestamp()
	case 1:
		exp := ToString(args[0])
		if !Blank(exp) {
			v, err := Parse(exp, Timestamp())
			if err == nil {
				return v
			}
		}
	case 2:
		exp := ToString(args[0])
		if !Blank(exp) {
			timeStamp := ToInt64(args[1])
			if timeStamp > 0 {
				v, err := Parse(exp, timeStamp)
				if err == nil {
					return v
				}
			}
		}
	}

	return 0
}

// Mkdir 创建一个目录，如果目录已存在则忽略
// export
func Mkdir(dir string, perm os.FileMode) error {
	if !FileExists(dir) {
		return os.Mkdir(dir, perm)
	}

	return nil
}

// FileExists 检测目录或者文件是否存在，返回 bool
// export
func FileExists(path string) bool {
	_, err := os.Stat(path)
	if err != nil && os.IsNotExist(err) {
		return false
	}
	return true
}

// WriteFile 写入文件
// export
func WriteFile(name string, data []byte, flag int, perm os.FileMode, sync bool) error {
	f, err := os.OpenFile(name, flag, perm)
	if err != nil {
		return err
	}

	_, err = f.Write(data)

	if sync {
		_ = f.Sync()
	}

	if err1 := f.Close(); err1 != nil && err == nil {
		err = err1
	}

	return err
}

// WriteFileAppend 追加写入文件
// export
func WriteFileAppend(name string, data []byte, perm os.FileMode, sync bool) error {
	return WriteFile(name, data, os.O_APPEND|os.O_CREATE|os.O_WRONLY, perm, sync)
}

const (
	reSpace    = "[ ]+"
	reSpaceOpt = "[ ]*"
	reMeridian = "(am|pm)"
	reHour24   = "(2[0-4]|[01]?[0-9])"
	reHour24lz = "([01][0-9]|2[0-4])"
	reHour12   = "(0?[1-9]|1[0-2])"
	reMinute   = "([0-5]?[0-9])"
	reMinutelz = "([0-5][0-9])"
	reSecond   = "(60|[0-5]?[0-9])"
	reSecondlz = "(60|[0-5][0-9])"
	reFrac     = "(?:\\.([0-9]+))"

	reDayfull = "sunday|monday|tuesday|wednesday|thursday|friday|saturday"
	reDayabbr = "sun|mon|tue|wed|thu|fri|sat"
	reDaytext = reDayfull + "|" + reDayabbr + "|weekdays?"

	reReltextnumber = "first|second|third|fourth|fifth|sixth|seventh|eighth?|ninth|tenth|eleventh|twelfth"
	reReltexttext   = "next|last|previous|this"
	reReltextunit   = "(?:second|sec|minute|min|hour|day|fortnight|forthnight|month|year)s?|weeks|" + reDaytext
	reRelmvttext    = "(back|front)"

	reYear          = "([0-9]{1,4})"
	reYear2         = "([0-9]{2})"
	reYear4         = "([0-9]{4})"
	reYear4withSign = "([+-]?[0-9]{4})"
	reMonth         = "(1[0-2]|0?[0-9])"
	reMonthlz       = "(0[0-9]|1[0-2])"
	reDay           = "(?:(3[01]|[0-2]?[0-9])(?:st|nd|rd|th)?)"
	reDaylz         = "(0[0-9]|[1-2][0-9]|3[01])"

	reMonthFull  = "january|february|march|april|may|june|july|august|september|october|november|december"
	reMonthAbbr  = "jan|feb|mar|apr|may|jun|jul|aug|sept?|oct|nov|dec"
	reMonthRoman = "i[vx]|vi{0,3}|xi{0,2}|i{1,3}"
	reMonthText  = "(" + reMonthFull + "|" + reMonthAbbr + "|" + reMonthRoman + ")"

	reTzCorrection = "((?:GMT)?([+-])" + reHour24 + ":?" + reMinute + "?)"
	reDayOfYear    = "(00[1-9]|0[1-9][0-9]|[12][0-9][0-9]|3[0-5][0-9]|36[0-6])"
	reWeekOfYear   = "(0[1-9]|[1-4][0-9]|5[0-3])"
)

type format struct {
	regex    string
	name     string
	callback func(r *result, inputs ...string) error
}

// export
func pointer(x int) *int {
	return &x
}

// export
func formats() []format {

	yesterday := format{
		regex: `(yesterday)`,
		name:  "yesterday",
		callback: func(r *result, inputs ...string) error {
			r.rd--
			// HACK: Original code had call to r.resetTime()
			// Might have to do with timezone adjustment
			return nil
		},
	}

	now := format{
		regex: `(now)`,
		name:  "now",
		callback: func(r *result, inputs ...string) error {
			return nil
		},
	}

	noon := format{
		regex: `(noon)`,
		name:  "noon",
		callback: func(r *result, inputs ...string) error {
			err := r.resetTime()
			if err != nil {
				return err
			}
			return r.time(12, 0, 0, 0)
		},
	}

	midnightOrToday := format{
		regex: `(midnight|today)`,
		name:  "midnight | today",
		callback: func(r *result, inputs ...string) error {
			return r.resetTime()
		},
	}

	tomorrow := format{
		regex: "(tomorrow)",
		name:  "tomorrow",
		callback: func(r *result, inputs ...string) error {
			r.rd++
			// Original code calls r.resetTime() here.
			return nil
		},
	}

	timestamp := format{
		regex: `^@(-?\d+)`,
		name:  "timestamp",
		callback: func(r *result, inputs ...string) error {
			s, err := strconv.Atoi(inputs[0])

			if err != nil {
				return err
			}

			r.rs += s
			r.y = pointer(1970)
			r.m = pointer(0)
			r.d = pointer(1)
			r.dates = 0

			return r.resetTime()
			// original code called r.zone(0)
		},
	}

	firstOrLastDay := format{
		regex: `^(first|last) day of`,
		name:  "firstdayof | lastdayof",
		callback: func(r *result, inputs ...string) error {
			if strings.ToLower(inputs[0]) == "first" {
				r.firstOrLastDayOfMonth = 1
				return nil
			}
			r.firstOrLastDayOfMonth = -1
			return nil
		},
	}

	// weekdayOf := format{
	// 	regex: "(?i)^(" + reReltextnumber + "|" + reReltexttext + ") (" + reDayfull + "|" + reDayabbr + ")" + " of",
	// 	name:  "weekdayof",
	// 	callback: func(r *result, inputs ...string) error {
	// 		relValue := inputs[0]
	// 		relUnit := inputs[1]
	// 		//TODO: implement handling of 'this time-unit'
	// 		amount, _ := lookupRelative(relValue)
	// 		return nil
	// 	},
	// 	//TODO:Implement
	// }

	backOrFrontOf := format{
		regex: "(?i)^(" + reMonthFull + ") " + reDaylz + " " + reYear + " " + reRelmvttext + " of " + reHour24 + reMeridian,
		name:  "backof | frontof",
		callback: func(r *result, inputs ...string) error {
			year, err := strconv.Atoi(inputs[2])
			if err != nil {
				return nil
			}
			day, err := strconv.Atoi(inputs[1])
			if err != nil {
				return nil
			}
			hour, err := strconv.Atoi(inputs[4])
			if err != nil {
				return err
			}
			r.m = pointer(lookupMonth(inputs[0]))
			r.y = pointer(year)
			r.d = pointer(day)

			minute, diffhour := lookupRelative(inputs[3])

			return r.time(processMeridian(hour+diffhour, inputs[5]), minute, 0, 0)
		},
	}

	mssqltime := format{
		regex: "(?i)^" + reHour24 + ":" + reMinutelz + ":" + reSecondlz + "[:.]([0-9]+)" + reMeridian + "?",
		name:  "mssqltime",
		callback: func(r *result, inputs ...string) error {

			hour, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			second, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}

			frac, err := strconv.Atoi(inputs[3][0:3])
			if err != nil {
				return err
			}

			if len(inputs) == 5 {
				meridian := inputs[4]
				hour = processMeridian(hour, meridian)
			}

			return r.time(hour, minute, second, frac)
		},
	}

	timeLong12 := format{
		regex: "(?i)^" + reHour12 + "[:.]" + reMinute + "[:.]" + reSecondlz + reSpaceOpt + reMeridian,
		name:  "timeLong12",
		callback: func(r *result, inputs ...string) error {

			hour, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			second, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}

			meridian := inputs[3]

			return r.time(processMeridian(hour, meridian), minute, second, 0)
		},
	}

	timeShort12 := format{
		regex: "(?i)^" + reHour12 + "[:.]" + reMinutelz + reSpaceOpt + reMeridian,
		name:  "timeShort12",
		callback: func(r *result, inputs ...string) error {

			hour, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			meridian := inputs[2]

			return r.time(processMeridian(hour, meridian), minute, 0, 0)
		},
	}

	timeTiny12 := format{
		regex: "(?i)^" + reHour12 + reSpaceOpt + reMeridian,
		name:  "timeTiny12",
		callback: func(r *result, inputs ...string) error {

			hour, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			meridian := inputs[1]

			return r.time(processMeridian(hour, meridian), 0, 0, 0)
		},
	}

	soap := format{
		regex: "^" + reYear4 + "-" + reMonthlz + "-" + reDaylz + "T" + reHour24lz + ":" + reMinutelz + ":" + reSecondlz + reFrac + "(z|Z)?" + reTzCorrection + "?",
		name:  "soap",
		callback: func(r *result, inputs ...string) error {

			year, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}
			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}
			day, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}
			hour, err := strconv.Atoi(inputs[3])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[4])
			if err != nil {
				return err
			}

			second, err := strconv.Atoi(inputs[5])
			if err != nil {
				return err
			}

			mili := inputs[6]

			if len(mili) > 3 {
				mili = mili[0:3]
			}

			frac, err := strconv.Atoi(mili)
			if err != nil {
				return err
			}

			tzCorrection := inputs[8]

			err = r.ymd(year, month-1, day)
			if err != nil {
				return err
			}
			err = r.time(hour, minute, second, frac)
			if err != nil {
				return err
			}
			if len(tzCorrection) > 0 {
				err := r.zone(processTzCorrection(tzCorrection, 0))
				if err != nil {
					return err
				}
			}
			return nil
		},
	}

	wddx := format{
		regex: "^" + reYear4 + "-" + reMonth + "-" + reDay + "T" + reHour24 + ":" + reMinute + ":" + reSecond + ".*",
		name:  "wddx",
		callback: func(r *result, inputs ...string) error {

			year, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}
			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}
			day, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}
			hour, err := strconv.Atoi(inputs[3])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[4])
			if err != nil {
				return err
			}

			second, err := strconv.Atoi(inputs[5])
			if err != nil {
				return err
			}

			err = r.ymd(year, month-1, day)
			if err != nil {
				return err
			}

			err = r.time(hour, minute, second, 0)
			return err
		},
	}

	exif := format{
		regex: "(?i)" + "^" + reYear4 + ":" + reMonthlz + ":" + reDaylz + " " + reHour24lz + ":" + reMinutelz + ":" + reSecondlz,
		name:  "exif",
		callback: func(r *result, inputs ...string) error {
			year, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}
			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}
			day, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}
			hour, err := strconv.Atoi(inputs[3])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[4])
			if err != nil {
				return err
			}

			second, err := strconv.Atoi(inputs[5])
			if err != nil {
				return err
			}

			err = r.ymd(year, month-1, day)
			if err != nil {
				return err
			}

			err = r.time(hour, minute, second, 0)
			return err
		},
	}

	xmlRpc := format{
		regex: "^" + reYear4 + reMonthlz + reDaylz + "T" + reHour24 + ":" + reMinutelz + ":" + reSecondlz,
		name:  "xmlrpc",
		callback: func(r *result, inputs ...string) error {
			year, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}
			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}
			day, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}
			hour, err := strconv.Atoi(inputs[3])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[4])
			if err != nil {
				return err
			}

			second, err := strconv.Atoi(inputs[5])
			if err != nil {
				return err
			}

			err = r.ymd(year, month-1, day)
			if err != nil {
				return err
			}

			err = r.time(+hour, +minute, +second, 0)
			return err
		},
	}

	xmlRpcNoColon := format{
		regex: "^" + reYear4 + reMonthlz + reDaylz + "[Tt]" + reHour24 + reMinutelz + reSecondlz,
		name:  "xmlrpcnocolon",
		callback: func(r *result, inputs ...string) error {
			year, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}
			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}
			day, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}
			hour, err := strconv.Atoi(inputs[3])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[4])
			if err != nil {
				return err
			}

			second, err := strconv.Atoi(inputs[5])
			if err != nil {
				return err
			}

			err = r.ymd(year, month-1, day)
			if err != nil {
				return err
			}

			err = r.time(hour, minute, second, 0)
			return err
		},
	}

	clf := format{
		regex: "(?i)^" + reDay + "/(" + reMonthAbbr + ")/" + reYear4 + ":" + reHour24lz + ":" + reMinutelz + ":" + reSecondlz + reSpace + reTzCorrection,
		name:  "clf",
		callback: func(r *result, inputs ...string) error {

			day, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			month := inputs[1]

			year, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}

			hour, err := strconv.Atoi(inputs[3])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[4])
			if err != nil {
				return err
			}

			second, err := strconv.Atoi(inputs[5])
			if err != nil {
				return err
			}

			tzCorrection := inputs[6]

			err = r.ymd(year, lookupMonth(month), day)
			if err != nil {
				return err
			}

			err = r.time(hour, minute, second, 0)
			if err != nil {
				return err
			}

			err = r.zone(processTzCorrection(tzCorrection, 0))
			return err
		},
	}

	iso8601long := format{
		regex: "^[Tt]?" + reHour24 + "[:.]" + reMinute + "[:.]" + reSecond + reFrac,
		name:  "iso8601long",
		callback: func(r *result, inputs ...string) error {

			hour, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			second, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}

			mili := inputs[3]

			if len(mili) > 3 {
				mili = mili[0:3]
			}

			frac, err := strconv.Atoi(mili)
			if err != nil {
				return err
			}
			return r.time(hour, minute, second, frac)
		},
	}

	dateTextual := format{
		regex: "(?i)^" + reMonthText + "[ .\\t-]*" + reDay + "[,.stndrh\\t ]+" + reYear,
		name:  "datetextual",
		callback: func(r *result, inputs ...string) error {

			month := inputs[0]

			day, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}
			year := inputs[2]
			y, err := processYear(year)
			if err != nil {
				return err
			}

			err = r.ymd(y, lookupMonth(month), day)
			return err
		},
	}

	pointedDate4 := format{
		regex: "^" + reDay + "[.\\t-]" + reMonth + "[.-]" + reYear4,
		name:  "pointeddate4",
		callback: func(r *result, inputs ...string) error {
			day, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			year, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}

			return r.ymd(year, month-1, day)
		},
	}

	pointedDate2 := format{
		regex: "^" + reDay + "[.\\t]" + reMonth + "\\." + reYear2,
		name:  "pointeddate2",
		callback: func(r *result, inputs ...string) error {
			day, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			y, err := processYear(inputs[2])
			if err != nil {
				return err
			}

			return r.ymd(y, month-1, day)
		},
	}

	datePointed := format{
		regex: "^" + reYear4 + "\\." + reMonth + "\\." + reDay + "\\.?",
		name:  "datePointed",
		callback: func(r *result, inputs ...string) error {
			year, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			day, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}
			return r.ymd(year, month-1, day)
		},
	}

	timeLong24 := format{
		regex: "^t?" + reHour24 + "[:.]" + reMinute + "[:.]" + reSecond,
		name:  "timelong24",
		callback: func(r *result, inputs ...string) error {

			hour, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			second, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}

			err = r.time(hour, minute, second, 0)
			return err
		},
	}

	dateNoColon := format{
		regex: "^" + reYear4 + reMonthlz + reDaylz,
		name:  "datenocolon",
		callback: func(r *result, inputs ...string) error {

			year, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			day, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}

			err = r.ymd(year, month-1, day)
			return err
		},
	}

	pgydotd := format{
		// also known as julian date format
		regex: "^" + reYear4 + `\.?` + reDayOfYear,
		name:  "pgydotd",
		callback: func(r *result, inputs ...string) error {
			year, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			day, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}
			return r.ymd(year, 0, day)
		},
	}

	timeShort24 := format{
		regex: "^t?" + reHour24 + "[:.]" + reMinute,
		name:  "timeshort24",
		callback: func(r *result, inputs ...string) error {
			hour, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}
			return r.time(hour, minute, 0, 0)
		},
	}

	iso8601noColon := format{
		regex: "^t?" + reHour24lz + reMinutelz + reSecondlz,
		name:  "iso8601nocolon",
		callback: func(r *result, inputs ...string) error {
			hour, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			second, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}

			return r.time(hour, minute, second, 0)
		},
	}

	dateSlash := format{
		regex: "^" + reYear4 + "/" + reMonth + "/" + reDay + "/?",
		name:  "dateslash",
		callback: func(r *result, inputs ...string) error {
			year, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			day, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}
			return r.ymd(year, month-1, day)
		},
	}

	american := format{
		regex: "^" + reMonth + "/" + reDay + "/" + reYear,
		name:  "american",
		callback: func(r *result, inputs ...string) error {
			month, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			day, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			year, err := processYear(inputs[2])
			if err != nil {
				return err
			}
			return r.ymd(year, month-1, +day)
		},
	}

	americanShort := format{
		regex: "^" + reMonth + "/" + reDay,
		name:  "americanshort",
		callback: func(r *result, inputs ...string) error {
			month, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			day, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			if r.dates > 0 {
				return fmt.Errorf("strtotime: The string contains two conflicting date/months")
			}

			r.dates++
			r.m = pointer(month - 1)
			r.d = pointer(day)

			return nil
		},
	}

	gnuDateShortOrIso8601date2 := format{
		// iso8601date2 is complete subset of gnudateshort
		regex: "^" + reYear + "-" + reMonth + "-" + reDay,
		name:  "gnudateshort | iso8601date2",
		callback: func(r *result, inputs ...string) error {
			year, err := processYear(inputs[0])

			if err != nil {
				return err
			}

			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			day, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}

			return r.ymd(year, month-1, day)
		},
	}

	iso8601date4 := format{
		regex: "^" + reYear4withSign + "-" + reMonthlz + "-" + reDaylz,
		name:  "iso8601date4",
		callback: func(r *result, inputs ...string) error {
			year, err := strconv.Atoi(inputs[0])

			if err != nil {
				return err
			}

			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			day, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}
			return r.ymd(year, month-1, day)
		},
	}

	gnuNoColon := format{
		regex: "^t" + reHour24lz + reMinutelz,
		name:  "gnunocolon",
		callback: func(r *result, inputs ...string) error {
			hour, err := strconv.Atoi(inputs[0])

			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			if r.times > 0 {
				return fmt.Errorf("strtotime: The string contains two conflicting hours")
			}

			r.times++
			r.i = pointer(minute)
			r.h = pointer(hour)
			r.s = pointer(0)
			return nil
		},
	}

	gnuDateShorter := format{
		regex: "^" + reYear4 + "-" + reMonth,
		name:  "gnudateshorter",
		callback: func(r *result, inputs ...string) error {
			year, err := strconv.Atoi(inputs[0])

			if err != nil {
				return err
			}

			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}
			return r.ymd(year, month-1, 1)
		},
	}

	pgTextReverse := format{
		// note: allowed years are from 32-9999
		// years below 32 should be treated as days in datefull
		regex: "(?i)^" + `(\d{3,4}|[4-9]\d|3[2-9])-(` + reMonthAbbr + ")-" + reDaylz,
		name:  "pgtextreverse",
		callback: func(r *result, inputs ...string) error {
			year, err := processYear(inputs[0])

			if err != nil {
				return err
			}

			month := lookupMonth(inputs[1])

			day, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}

			return r.ymd(year, month, day)
		},
	}

	dateFull := format{
		regex: "(?i)^" + reDay + `[ \t.-]*` + reMonthText + `[ \t.-]*` + reYear,
		name:  "datefull",
		callback: func(r *result, inputs ...string) error {

			day, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			month := lookupMonth(inputs[1])

			year, err := processYear(inputs[2])

			if err != nil {
				return err
			}

			return r.ymd(year, month, day)
		},
	}

	dateNoDay := format{
		regex: "(?i)^" + reMonthText + `[ .\t-]*` + reYear4,
		name:  "datenoday",
		callback: func(r *result, inputs ...string) error {
			month := lookupMonth(inputs[0])

			year, err := processYear(inputs[1])

			if err != nil {
				return err
			}

			return r.ymd(year, month, 1)
		},
	}

	dateNoDayRev := format{
		regex: "(?i)^" + reYear4 + `[ .\t-]*` + reMonthText,
		name:  "datenodayrev",
		callback: func(r *result, inputs ...string) error {
			year, err := processYear(inputs[0])

			if err != nil {
				return err
			}

			month := lookupMonth(inputs[1])

			return r.ymd(year, month, 1)
		},
	}

	pgTextShort := format{
		regex: "(?i)^(" + reMonthAbbr + ")-" + reDaylz + "-" + reYear,
		name:  "pgtextshort",
		callback: func(r *result, inputs ...string) error {

			month := lookupMonth(inputs[0])

			day, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			year, err := processYear(inputs[2])

			if err != nil {
				return err
			}

			return r.ymd(year, month, day)
		},
	}

	dateNoYear := format{
		regex: "(?i)^" + reMonthText + `[ .\t-]*` + reDay + `[,.stndrh\t ]*`,
		name:  "datenoyear",
		callback: func(r *result, inputs ...string) error {

			if r.dates > 0 {
				return fmt.Errorf("strtotime: The string contains two conflicting date/months")
			}

			r.dates++

			month := lookupMonth(inputs[0])

			day, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			r.m = pointer(month)
			r.d = pointer(day)
			return nil
		},
	}

	dateNoYearRev := format{
		regex: "(?i)^" + reDay + `[ .\t-]*` + reMonthText,
		name:  "datenoyearrev",
		callback: func(r *result, inputs ...string) error {

			if r.dates > 0 {
				return fmt.Errorf("strtotime: The string contains two conflicting date/months")
			}
			r.dates++

			day, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			month := lookupMonth(inputs[1])

			r.m = pointer(month)
			r.d = pointer(day)
			return nil
		},
	}

	isoWeekDay := format{
		regex: "^" + reYear4 + "-?W" + reWeekOfYear + `(?:-?([0-7]))?`,
		name:  "isoweekday",
		callback: func(r *result, inputs ...string) error {

			day := 1

			if len(inputs) > 2 {
				d, err := strconv.Atoi(inputs[2])
				if err != nil {
					return err
				}
				day = d
			}

			year, err := strconv.Atoi(inputs[0])

			if err != nil {
				return err
			}

			week, err := strconv.Atoi(inputs[1])

			if err != nil {
				return err
			}

			// reset date to January 1st of given year
			err = r.ymd(year, 0, 1)

			if err != nil {
				return err
			}

			// get weekday for Jan 1st
			weekday := time.Date(year, time.January, 1, 0, 0, 0, 0, time.Local).Weekday()

			// and use the day to figure out the offset for day 1 of week 1
			diff := int(weekday)
			if diff > 4 {
				diff = -(diff - 7)
			} else {
				diff = -diff
			}
			// rd is number of days after Jan 1st
			r.rd += diff + ((week - 1) * 7) + day
			return nil
		},
	}

	relativeText := format{
		regex: "(?i)^(" + reReltextnumber + "|" + reReltexttext + ")" + reSpace + "(" + reReltextunit + ")",
		name:  "relativetext",
		callback: func(r *result, inputs ...string) error {
			relValue := inputs[0]
			relUnit := inputs[1]
			// TODO: implement handling of 'this time-unit'
			amount, _ := lookupRelative(relValue)

			switch strings.ToLower(relUnit) {
			case "sec", "secs", "second", "seconds":
				r.rs += amount
				//break
			case "min", "mins", "minute", "minutes":
				r.ri += amount
				//break
			case "hour", "hours":
				r.rh += amount
				//break
			case "day", "days":
				r.rd += amount
				//break
			case "fortnight", "fortnights", "forthnight", "forthnights":
				r.rd += amount * 14
				//break
			case "week", "weeks":
				r.rd += amount * 7
				//break
			case "month", "months":
				r.rm += amount
				//break
			case "year", "years":
				r.ry += amount
				//break
			case "mon", "monday", "tue", "tuesday", "wed", "wednesday", "thu", "thursday", "fri", "friday", "sat", "saturday", "sun", "sunday":
				err := r.resetTime()
				if err != nil {
					return err
				}
				r.weekday = pointer(lookupWeekday(relUnit, 7))
				r.weekdayBehavior = 1
				if amount > 0 {
					r.rd += (amount - 1) * 7
				}
				if amount <= 0 {
					r.rd += amount * 7
				}
				//break
			case "weekday", "weekdays":
				// TODO: Implement
				//break
			}
			return nil
		},
	}

	relative := format{
		regex: "(?i)^([+-]*)[ \\t]*(\\d+)" + reSpaceOpt + "(" + reReltextunit + "|week)",
		name:  "relative",
		callback: func(r *result, inputs ...string) error {
			signs := inputs[0]

			relValue, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}
			relUnit := inputs[2]
			minuses := float64(strings.Count(signs, "-"))
			amount := relValue * int(math.Pow(float64(-1), minuses))

			switch strings.ToLower(relUnit) {
			case "sec", "secs", "second", "seconds":
				r.rs += amount
				//break
			case "min", "mins", "minute", "minutes":
				r.ri += amount
				//break
			case "hour", "hours":
				r.rh += amount
				//break
			case "day", "days":
				r.rd += amount
				//break
			case "fortnight", "fortnights", "forthnight", "forthnights":
				r.rd += amount * 14
				//break
			case "week", "weeks":
				r.rd += amount * 7
				//break
			case "month", "months":
				r.rm += amount
				//break
			case "year", "years":
				r.ry += amount
				//break
			case "mon", "monday", "tue", "tuesday", "wed", "wednesday", "thu", "thursday", "fri", "friday", "sat", "saturday", "sun", "sunday":
				err := r.resetTime()
				if err != nil {
					return err
				}
				r.weekday = pointer(lookupWeekday(relUnit, 7))
				r.weekdayBehavior = 1
				rd := amount * 7
				if amount > 0 {
					rd = (amount - 1) * 7
				}
				r.rd += rd
				//break
			case "weekday", "weekdays":
				// todo
				//break
			}
			return nil
		},
	}

	dayText := format{
		regex: "(?i)^(" + reDaytext + ")",
		name:  "daytext",
		callback: func(r *result, inputs ...string) error {
			err := r.resetTime()
			if err != nil {
				return err
			}
			r.weekday = pointer(lookupWeekday(inputs[0], 0))

			if r.weekdayBehavior != 2 {
				r.weekdayBehavior = 1
			}
			return nil
		},
	}

	relativeTextWeek := format{
		regex: "(?i)^(" + reReltexttext + ")" + reSpace + "week",
		name:  "relativetextweek",
		callback: func(r *result, inputs ...string) error {
			r.weekdayBehavior = 2

			switch strings.ToLower(inputs[0]) {
			case "this":
				r.rd += 0
				//break
			case "next":
				r.rd += 7
				//break
			case "last", "previous":
				r.rd -= 7
				//break
			}

			if r.weekday == nil {
				r.weekday = pointer(1)
			}
			return nil
		},
	}

	monthFullOrMonthAbbr := format{
		regex: "(?i)^(" + reMonthFull + "|" + reMonthAbbr + ")",
		name:  "monthfull | monthabbr",
		callback: func(r *result, inputs ...string) error {
			month := inputs[0]
			if r.dates > 0 {
				return fmt.Errorf("strtotime: The string contains two conflicting date/months")
			}
			r.dates++
			r.m = pointer(lookupMonth(month))
			return nil
		},
	}

	tzCorrection := format{
		regex: "(?i)^" + reTzCorrection,
		name:  "tzcorrection",
		callback: func(r *result, inputs ...string) error {
			return r.zone(processTzCorrection(inputs[0], 0))
		},
	}

	ago := format{
		regex: "(?i)^ago",
		name:  "ago",
		callback: func(r *result, inputs ...string) error {
			r.ry = -r.ry
			r.rm = -r.rm
			r.rd = -r.rd
			r.rh = -r.rh
			r.ri = -r.ri
			r.rs = -r.rs
			r.rf = -r.rf
			return nil
		},
	}

	gnuNoColon2 := format{
		// second instance of gnunocolon, without leading 't'
		// it's down here, because it is very generic (4 digits in a row)
		// thus conflicts with many rules above
		// only year4 should come afterwards
		regex: "(?i)^" + reHour24lz + reMinutelz,
		name:  "gnunocolon",
		callback: func(r *result, inputs ...string) error {

			hour, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			f := r.f

			if f == nil {
				f = pointer(0)
			}

			return r.time(hour, minute, 0, *f)
		},
	}

	year4 := format{
		regex: "^" + reYear4,
		name:  "year4",
		callback: func(r *result, inputs ...string) error {

			year, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			r.y = pointer(year)

			return nil
		},
	}

	whitespace := format{
		regex: "^[ .,\t]+",
		name:  "whitespace",
		callback: func(r *result, inputs ...string) error {
			return nil
		},
	}

	zhYMDformat := format{
		// 匹配中文年月日
		regex: "^" + reYear + "年" + reMonth + "月" + reDay + "(日)?",
		name:  "zhformat",
		callback: func(r *result, inputs ...string) error {
			year, err := processYear(inputs[0])

			if err != nil {
				return err
			}

			month, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			day, err := strconv.Atoi(inputs[2])
			if err != nil {
				return err
			}

			return r.ymd(year, month-1, day)
		},
	}

	zhHMSformat := format{
		// 匹配中文时分秒
		regex: "^" + reHour24 + "[时|点]" + reMinute + "分" + reSecond + "?(秒)?",
		name:  "zhHMS",
		callback: func(r *result, inputs ...string) error {

			hour, err := strconv.Atoi(inputs[0])
			if err != nil {
				return err
			}

			minute, err := strconv.Atoi(inputs[1])
			if err != nil {
				return err
			}

			second := 0
			if inputs[2] != "" {
				second, err = strconv.Atoi(inputs[2])
				if err != nil {
					return err
				}
			}

			err = r.time(hour, minute, second, 0)
			return err
		},
	}

	formats := []format{
		zhYMDformat,
		zhHMSformat,
		yesterday,
		now,
		noon,
		midnightOrToday,
		tomorrow,
		timestamp,
		firstOrLastDay,
		backOrFrontOf,
		// weekdayOf,
		mssqltime,
		timeLong12,
		timeShort12,
		timeTiny12,
		soap,
		wddx,
		exif,
		xmlRpc,
		xmlRpcNoColon,
		clf,
		iso8601long,
		dateTextual,
		pointedDate4,
		pointedDate2,
		datePointed,
		timeLong24,
		dateNoColon,
		pgydotd,
		timeShort24,
		iso8601noColon,
		dateSlash,
		american,
		americanShort,
		gnuDateShortOrIso8601date2,
		iso8601date4,
		gnuNoColon,
		gnuDateShorter,
		pgTextReverse,
		dateFull,
		dateNoDay,
		dateNoDayRev,
		pgTextShort,
		dateNoYear,
		dateNoYearRev,
		isoWeekDay,
		relativeText,
		relative,
		dayText,
		relativeTextWeek,
		monthFullOrMonthAbbr,
		tzCorrection,
		ago,
		gnuNoColon2,
		year4,
		whitespace,
	}

	return formats
}

// GenInteger 整型范型集合
type GenInteger interface {
	int | int8 | int16 | int32 | int64 | uint | uint8 | uint16 | uint32 | uint64
}

// GenFloat 浮点型范型集合
type GenFloat interface {
	float32 | float64
}

// GenNumber 数值范型集合
type GenNumber interface {
	GenInteger | GenFloat
}

// MemoryBytes 返回当前主要的内存指标信息 (ReadMemStats 会 stopTheWorld, 谨慎非频繁使用)
// export
func MemoryBytes() map[string]int64 {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	maps := make(map[string]int64)
	maps["sys"] = int64(m.Sys)
	maps["heapSys"] = int64(m.HeapSys)
	maps["heapInuse"] = int64(m.HeapInuse)
	maps["heapAlloc"] = int64(m.HeapAlloc)

	return maps
}

// Memory 指定格式返回当前主要的内存指标信息, (ReadMemStats 会 stopTheWorld, 谨慎非频繁使用)
// export
func Memory(format string) map[string]int64 {
	m := MemoryBytes()
	for k, v := range m {
		if v > 0 {
			switch format {
			case SizeB:
				m[k] = v
			case SizeKB:
				m[k] = v / BytesPerKB
			case SizeMB:
				m[k] = v / BytesPerMB
			case SizeGB:
				m[k] = v / BytesPerGB
			case SizeTB:
				m[k] = v / BytesPerTB
			case SizePB:
				m[k] = v / BytesPerPB
			case SizeEB:
				m[k] = v / BytesPerEB
			default:
				m[k] = v
			}
		}
	}

	return m
}

// EmptyAll 判断是否全部为空
// export
func EmptyAll(values ...any) bool {
	if len(values) == 0 {
		return true
	}

	for _, v := range values {
		if !Empty(v) {
			return false
		}
	}

	return true
}

// EmptyAny 判断是否任意一个为空
// export
func EmptyAny(values ...any) bool {
	if len(values) == 0 {
		return true
	}

	for _, v := range values {
		if Empty(v) {
			return true
		}
	}

	return false
}

// Empty 判断是否为空, 支持字符串、数值、数组、Slice、Map
// export
func Empty(value any) bool {
	if value == nil {
		return true
	}

	switch value.(type) {
	case string:
		return value == ""
	case int, int8, int16, int32, int64:
		return value == 0
	case uint, uint8, uint16, uint32, uint64:
		return value == 0
	case float32, float64:
		return value == 0
	case bool:
		return value == false
	default:
		r := reflect.ValueOf(value)
		switch r.Kind() {
		case reflect.Slice, reflect.Map:
			return r.Len() == 0 || r.IsNil()
		case reflect.Array:
			return r.Len() == 0
		case reflect.Ptr, reflect.Interface:
			return r.IsNil()
		}
	}

	return false
}

// Bytes 更高效的字符串转字节数组
// export
func Bytes(s string) []byte {
	return *(*[]byte)(unsafe.Pointer(
		&struct {
			string
			Cap int
		}{s, len(s)},
	))
}

// String 更高效的字节数组转字符串
// export
func String(b []byte) string {
	return *(*string)(unsafe.Pointer(&b))
}

// Command 执行系统命令
// export
func Command(bin string, argv []string, baseDir string) ([]byte, error) {
	cmd := exec.Command(bin, argv...)

	if baseDir != "" {
		cmd.Dir = baseDir
	}

	var stdout bytes.Buffer
	var stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr

	err := cmd.Run()

	if err != nil {
		return stdout.Bytes(), fmt.Errorf("%s: %s", err, stderr.Bytes())
	}

	return stdout.Bytes(), nil
}

// If 三元运算符
// export
func If[T any](condition bool, trueVal, falseVal T) T {
	if condition {
		return trueVal
	}

	return falseVal
}

// export
func Md5(str string) string {
	hexStr := md5.Sum(Bytes(str))

	return hex.EncodeToString(hexStr[:])
}

// Md5Bit16 返回 16位 字符串 Md5 值
// export
func Md5Bit16(str string) string {
	s := Md5(str)
	return SubString(s, 8, 16)
}

// Sha1 返回字符串 Sha1 值
// export
func Sha1(str string) string {
	hexStr := sha1.Sum(Bytes(str))

	return hex.EncodeToString(hexStr[:])
}

// Sha256 返回字符串 Sha256 值
// export
func Sha256(str string) string {
	hexStr := sha256.Sum256(Bytes(str))

	return hex.EncodeToString(hexStr[:])
}

// Sha384 返回字符串 Sha384 值
// export
func Sha384(str string) string {
	hexStr := sha512.Sum384(Bytes(str))

	return hex.EncodeToString(hexStr[:])
}

// Sha512 返回字符串 Sha512 值
// export
func Sha512(str string) string {
	hexStr := sha512.Sum512(Bytes(str))

	return hex.EncodeToString(hexStr[:])
}

// Base64Encode 返回字符串 Base64 值
// export
func Base64Encode(str string) string {
	return base64.StdEncoding.EncodeToString(Bytes(str))
}

// Base64Decode 返回 Base64 值对应的字符串
// export
func Base64Decode(str string) string {
	decode, _ := base64.StdEncoding.DecodeString(str)

	return String(decode)
}

// Base64UrlEncode 返回字符串 Url Safe Base64 值
// export
func Base64UrlEncode(str string) string {
	return base64.URLEncoding.EncodeToString(Bytes(str))
}

// Base64UrlDecode 返回 Url Safe Base64 值对应的字符串
// export
func Base64UrlDecode(str string) string {
	decode, _ := base64.URLEncoding.DecodeString(str)

	return String(decode)
}

// UserAgentRandom generates a random DESKTOP browser user-agent on every requests
// export
func UserAgentRandom() string {
	return uaGens[rand.Intn(len(uaGens))]()
}

// UserAgentRandomMobile generates a random MOBILE browser user-agent on every requests
// export
func UserAgentRandomMobile() string {
	return uaGensMobile[rand.Intn(len(uaGensMobile))]()

}

var uaGens = []func() string{
	genFirefoxUA,
	genChromeUA,
	genEdgeUA,
	genOperaUA,
}

var uaGensMobile = []func() string{
	genMobilePixel7UA,
	genMobilePixel6UA,
	genMobilePixel5UA,
	genMobilePixel4UA,
	genMobileNexus10UA,
}

// RandomUserAgent generates a random DESKTOP browser user-agent on every requests

var ffVersions = []float32{
	// NOTE: Only version released after Jun 1, 2022 will be listed.
	// Data source: https://en.wikipedia.org/wiki/Firefox_version_history

	// 2022
	102.0,
	103.0,
	104.0,
	105.0,
	106.0,
	107.0,
	108.0,

	// 2023
	109.0,
	110.0,
	111.0,
	112.0,
	113.0,
}

var chromeVersions = []string{
	// NOTE: Only version released after Jun 1, 2022 will be listed.
	// Data source: https://chromereleases.googleblog.com/search/label/Stable%20updates

	// https://chromereleases.googleblog.com/2022/06/stable-channel-update-for-desktop.html
	"102.0.5005.115",

	// https://chromereleases.googleblog.com/2022/06/stable-channel-update-for-desktop_21.html
	"103.0.5060.53",

	// https://chromereleases.googleblog.com/2022/06/stable-channel-update-for-desktop_27.html
	"103.0.5060.66",

	// https://chromereleases.googleblog.com/2022/07/stable-channel-update-for-desktop.html
	"103.0.5060.114",

	// https://chromereleases.googleblog.com/2022/07/stable-channel-update-for-desktop_19.html
	"103.0.5060.134",

	// https://chromereleases.googleblog.com/2022/08/stable-channel-update-for-desktop.html
	"104.0.5112.79",
	"104.0.5112.80",
	"104.0.5112.81",

	// https://chromereleases.googleblog.com/2022/08/stable-channel-update-for-desktop_16.html
	"104.0.5112.101",
	"104.0.5112.102",

	// https://chromereleases.googleblog.com/2022/08/stable-channel-update-for-desktop_30.html
	"105.0.5195.52",
	"105.0.5195.53",
	"105.0.5195.54",

	// https://chromereleases.googleblog.com/2022/09/stable-channel-update-for-desktop.html
	"105.0.5195.102",

	// https://chromereleases.googleblog.com/2022/09/stable-channel-update-for-desktop_14.html
	"105.0.5195.125",
	"105.0.5195.126",
	"105.0.5195.127",

	// https://chromereleases.googleblog.com/2022/09/stable-channel-update-for-desktop_27.html
	"106.0.5249.61",
	"106.0.5249.62",

	// https://chromereleases.googleblog.com/2022/09/stable-channel-update-for-desktop_30.html
	"106.0.5249.91",

	// https://chromereleases.googleblog.com/2022/10/stable-channel-update-for-desktop.html
	"106.0.5249.103",

	// https://chromereleases.googleblog.com/2022/10/stable-channel-update-for-desktop_11.html
	"106.0.5249.119",

	// https://chromereleases.googleblog.com/2022/10/stable-channel-update-for-desktop_25.html
	"107.0.5304.62",
	"107.0.5304.63",
	"107.0.5304.68",

	// https://chromereleases.googleblog.com/2022/10/stable-channel-update-for-desktop_27.html
	"107.0.5304.87",
	"107.0.5304.88",

	// https://chromereleases.googleblog.com/2022/11/stable-channel-update-for-desktop.html
	"107.0.5304.106",
	"107.0.5304.107",
	"107.0.5304.110",

	// https://chromereleases.googleblog.com/2022/11/stable-channel-update-for-desktop_24.html
	"107.0.5304.121",
	"107.0.5304.122",

	// https://chromereleases.googleblog.com/2022/11/stable-channel-update-for-desktop_29.html
	"108.0.5359.71",
	"108.0.5359.72",

	// https://chromereleases.googleblog.com/2022/12/stable-channel-update-for-desktop.html
	"108.0.5359.94",
	"108.0.5359.95",

	// https://chromereleases.googleblog.com/2022/12/stable-channel-update-for-desktop_7.html
	"108.0.5359.98",
	"108.0.5359.99",

	// https://chromereleases.googleblog.com/2022/12/stable-channel-update-for-desktop_13.html
	"108.0.5359.124",
	"108.0.5359.125",

	// https://chromereleases.googleblog.com/2023/01/stable-channel-update-for-desktop.html
	"109.0.5414.74",
	"109.0.5414.75",
	"109.0.5414.87",

	// https://chromereleases.googleblog.com/2023/01/stable-channel-update-for-desktop_24.html
	"109.0.5414.119",
	"109.0.5414.120",

	// https://chromereleases.googleblog.com/2023/02/stable-channel-update-for-desktop.html
	"110.0.5481.77",
	"110.0.5481.78",

	// https://chromereleases.googleblog.com/2023/02/stable-channel-desktop-update.html
	"110.0.5481.96",
	"110.0.5481.97",

	// https://chromereleases.googleblog.com/2023/02/stable-channel-desktop-update_14.html
	"110.0.5481.100",

	// https://chromereleases.googleblog.com/2023/02/stable-channel-desktop-update_16.html
	"110.0.5481.104",

	// https://chromereleases.googleblog.com/2023/02/stable-channel-desktop-update_22.html
	"110.0.5481.177",
	"110.0.5481.178",

	// https://chromereleases.googleblog.com/2023/02/stable-channel-desktop-update_97.html
	"109.0.5414.129",

	// https://chromereleases.googleblog.com/2023/03/stable-channel-update-for-desktop.html
	"111.0.5563.64",
	"111.0.5563.65",

	// https://chromereleases.googleblog.com/2023/03/stable-channel-update-for-desktop_21.html
	"111.0.5563.110",
	"111.0.5563.111",

	// https://chromereleases.googleblog.com/2023/03/stable-channel-update-for-desktop_27.html
	"111.0.5563.146",
	"111.0.5563.147",

	// https://chromereleases.googleblog.com/2023/04/stable-channel-update-for-desktop.html
	"112.0.5615.49",
	"112.0.5615.50",

	// https://chromereleases.googleblog.com/2023/04/stable-channel-update-for-desktop_12.html
	"112.0.5615.86",
	"112.0.5615.87",

	// https://chromereleases.googleblog.com/2023/04/stable-channel-update-for-desktop_14.html
	"112.0.5615.121",

	// https://chromereleases.googleblog.com/2023/04/stable-channel-update-for-desktop_18.html
	"112.0.5615.137",
	"112.0.5615.138",
	"112.0.5615.165",

	// https://chromereleases.googleblog.com/2023/05/stable-channel-update-for-desktop.html
	"113.0.5672.63",
	"113.0.5672.64",

	// https://chromereleases.googleblog.com/2023/05/stable-channel-update-for-desktop_8.html
	"113.0.5672.92",
	"113.0.5672.93",
}

var edgeVersions = []string{
	// NOTE: Only version released after Jun 1, 2022 will be listed.
	// Data source: https://learn.microsoft.com/en-us/deployedge/microsoft-edge-release-schedule

	// 2022
	"103.0.0.0,103.0.1264.37",
	"104.0.0.0,104.0.1293.47",
	"105.0.0.0,105.0.1343.25",
	"106.0.0.0,106.0.1370.34",
	"107.0.0.0,107.0.1418.24",
	"108.0.0.0,108.0.1462.42",

	// 2023
	"109.0.0.0,109.0.1518.49",
	"110.0.0.0,110.0.1587.41",
	"111.0.0.0,111.0.1661.41",
	"112.0.0.0,112.0.1722.34",
	"113.0.0.0,113.0.1774.3",
}

var operaVersions = []string{
	// NOTE: Only version released after Jan 1, 2023 will be listed.
	// Data source: https://blogs.opera.com/desktop/

	// https://blogs.opera.com/desktop/changelog-for-96/
	"110.0.5449.0,96.0.4640.0",
	"110.0.5464.2,96.0.4653.0",
	"110.0.5464.2,96.0.4660.0",
	"110.0.5481.30,96.0.4674.0",
	"110.0.5481.30,96.0.4691.0",
	"110.0.5481.30,96.0.4693.12",
	"110.0.5481.77,96.0.4693.16",
	"110.0.5481.100,96.0.4693.20",
	"110.0.5481.178,96.0.4693.31",
	"110.0.5481.178,96.0.4693.50",
	"110.0.5481.192,96.0.4693.80",

	// https://blogs.opera.com/desktop/changelog-for-97/
	"111.0.5532.2,97.0.4711.0",
	"111.0.5532.2,97.0.4704.0",
	"111.0.5532.2,97.0.4697.0",
	"111.0.5562.0,97.0.4718.0",
	"111.0.5563.19,97.0.4719.4",
	"111.0.5563.19,97.0.4719.11",
	"111.0.5563.41,97.0.4719.17",
	"111.0.5563.65,97.0.4719.26",
	"111.0.5563.65,97.0.4719.28",
	"111.0.5563.111,97.0.4719.43",
	"111.0.5563.147,97.0.4719.63",
	"111.0.5563.147,97.0.4719.83",

	// https://blogs.opera.com/desktop/changelog-for-98/
	"112.0.5596.2,98.0.4756.0",
	"112.0.5596.2,98.0.4746.0",
	"112.0.5615.20,98.0.4759.1",
	"112.0.5615.50,98.0.4759.3",
	"112.0.5615.87,98.0.4759.6",
	"112.0.5615.165,98.0.4759.15",
	"112.0.5615.165,98.0.4759.21",
	"112.0.5615.165,98.0.4759.39",
}

var pixel7AndroidVersions = []string{
	// Data source:
	// - https://developer.android.com/about/versions
	// - https://source.android.com/docs/setup/about/build-numbers#source-code-tags-and-builds
	"13",
}

var pixel6AndroidVersions = []string{
	// Data source:
	// - https://developer.android.com/about/versions
	// - https://source.android.com/docs/setup/about/build-numbers#source-code-tags-and-builds
	"12",
	"13",
}

var pixel5AndroidVersions = []string{
	// Data source:
	// - https://developer.android.com/about/versions
	// - https://source.android.com/docs/setup/about/build-numbers#source-code-tags-and-builds
	"11",
	"12",
	"13",
}

var pixel4AndroidVersions = []string{
	// Data source:
	// - https://developer.android.com/about/versions
	// - https://source.android.com/docs/setup/about/build-numbers#source-code-tags-and-builds
	"10",
	"11",
	"12",
	"13",
}

var nexus10AndroidVersions = []string{
	// Data source:
	// - https://developer.android.com/about/versions
	// - https://source.android.com/docs/setup/about/build-numbers#source-code-tags-and-builds
	"4.4.2",
	"4.4.4",
	"5.0",
	"5.0.1",
	"5.0.2",
	"5.1",
	"5.1.1",
}

var nexus10Builds = []string{
	// Data source: https://source.android.com/docs/setup/about/build-numbers#source-code-tags-and-builds

	"LMY49M", // android-5.1.1_r38 (Lollipop)
	"LMY49J", // android-5.1.1_r37 (Lollipop)
	"LMY49I", // android-5.1.1_r36 (Lollipop)
	"LMY49H", // android-5.1.1_r35 (Lollipop)
	"LMY49G", // android-5.1.1_r34 (Lollipop)
	"LMY49F", // android-5.1.1_r33 (Lollipop)
	"LMY48Z", // android-5.1.1_r30 (Lollipop)
	"LMY48X", // android-5.1.1_r25 (Lollipop)
	"LMY48T", // android-5.1.1_r19 (Lollipop)
	"LMY48M", // android-5.1.1_r14 (Lollipop)
	"LMY48I", // android-5.1.1_r9 (Lollipop)
	"LMY47V", // android-5.1.1_r1 (Lollipop)
	"LMY47D", // android-5.1.0_r1 (Lollipop)
	"LRX22G", // android-5.0.2_r1 (Lollipop)
	"LRX22C", // android-5.0.1_r1 (Lollipop)
	"LRX21P", // android-5.0.0_r4.0.1 (Lollipop)
	"KTU84P", // android-4.4.4_r1 (KitKat)
	"KTU84L", // android-4.4.3_r1 (KitKat)
	"KOT49H", // android-4.4.2_r1 (KitKat)
	"KOT49E", // android-4.4.1_r1 (KitKat)
	"KRT16S", // android-4.4_r1.2 (KitKat)
	"JWR66Y", // android-4.3_r1.1 (Jelly Bean)
	"JWR66V", // android-4.3_r1 (Jelly Bean)
	"JWR66N", // android-4.3_r0.9.1 (Jelly Bean)
	"JDQ39 ", // android-4.2.2_r1 (Jelly Bean)
	"JOP40F", // android-4.2.1_r1.1 (Jelly Bean)
	"JOP40D", // android-4.2.1_r1 (Jelly Bean)
	"JOP40C", // android-4.2_r1 (Jelly Bean)
}

var osStrings = []string{
	// MacOS - High Sierra
	"Macintosh; Intel Mac OS X 10_13",
	"Macintosh; Intel Mac OS X 10_13_1",
	"Macintosh; Intel Mac OS X 10_13_2",
	"Macintosh; Intel Mac OS X 10_13_3",
	"Macintosh; Intel Mac OS X 10_13_4",
	"Macintosh; Intel Mac OS X 10_13_5",
	"Macintosh; Intel Mac OS X 10_13_6",

	// MacOS - Mojave
	"Macintosh; Intel Mac OS X 10_14",
	"Macintosh; Intel Mac OS X 10_14_1",
	"Macintosh; Intel Mac OS X 10_14_2",
	"Macintosh; Intel Mac OS X 10_14_3",
	"Macintosh; Intel Mac OS X 10_14_4",
	"Macintosh; Intel Mac OS X 10_14_5",
	"Macintosh; Intel Mac OS X 10_14_6",

	// MacOS - Catalina
	"Macintosh; Intel Mac OS X 10_15",
	"Macintosh; Intel Mac OS X 10_15_1",
	"Macintosh; Intel Mac OS X 10_15_2",
	"Macintosh; Intel Mac OS X 10_15_3",
	"Macintosh; Intel Mac OS X 10_15_4",
	"Macintosh; Intel Mac OS X 10_15_5",
	"Macintosh; Intel Mac OS X 10_15_6",
	"Macintosh; Intel Mac OS X 10_15_7",

	// MacOS - Big Sur
	"Macintosh; Intel Mac OS X 11_0",
	"Macintosh; Intel Mac OS X 11_0_1",
	"Macintosh; Intel Mac OS X 11_1",
	"Macintosh; Intel Mac OS X 11_2",
	"Macintosh; Intel Mac OS X 11_2_1",
	"Macintosh; Intel Mac OS X 11_2_2",
	"Macintosh; Intel Mac OS X 11_2_3",
	"Macintosh; Intel Mac OS X 11_3",
	"Macintosh; Intel Mac OS X 11_3_1",
	"Macintosh; Intel Mac OS X 11_4",
	"Macintosh; Intel Mac OS X 11_5",
	"Macintosh; Intel Mac OS X 11_5_1",
	"Macintosh; Intel Mac OS X 11_5_2",
	"Macintosh; Intel Mac OS X 11_6",
	"Macintosh; Intel Mac OS X 11_6_1",
	"Macintosh; Intel Mac OS X 11_6_2",
	"Macintosh; Intel Mac OS X 11_6_3",
	"Macintosh; Intel Mac OS X 11_6_4",
	"Macintosh; Intel Mac OS X 11_6_5",
	"Macintosh; Intel Mac OS X 11_6_6",
	"Macintosh; Intel Mac OS X 11_6_7",
	"Macintosh; Intel Mac OS X 11_6_8",
	"Macintosh; Intel Mac OS X 11_7",
	"Macintosh; Intel Mac OS X 11_7_1",
	"Macintosh; Intel Mac OS X 11_7_2",
	"Macintosh; Intel Mac OS X 11_7_3",
	"Macintosh; Intel Mac OS X 11_7_4",
	"Macintosh; Intel Mac OS X 11_7_5",
	"Macintosh; Intel Mac OS X 11_7_6",

	// MacOS - Monterey
	"Macintosh; Intel Mac OS X 12_0",
	"Macintosh; Intel Mac OS X 12_0_1",
	"Macintosh; Intel Mac OS X 12_1",
	"Macintosh; Intel Mac OS X 12_2",
	"Macintosh; Intel Mac OS X 12_2_1",
	"Macintosh; Intel Mac OS X 12_3",
	"Macintosh; Intel Mac OS X 12_3_1",
	"Macintosh; Intel Mac OS X 12_4",
	"Macintosh; Intel Mac OS X 12_5",
	"Macintosh; Intel Mac OS X 12_5_1",
	"Macintosh; Intel Mac OS X 12_6",
	"Macintosh; Intel Mac OS X 12_6_1",
	"Macintosh; Intel Mac OS X 12_6_2",
	"Macintosh; Intel Mac OS X 12_6_3",
	"Macintosh; Intel Mac OS X 12_6_4",
	"Macintosh; Intel Mac OS X 12_6_5",

	// MacOS - Ventura
	"Macintosh; Intel Mac OS X 13_0",
	"Macintosh; Intel Mac OS X 13_0_1",
	"Macintosh; Intel Mac OS X 13_1",
	"Macintosh; Intel Mac OS X 13_2",
	"Macintosh; Intel Mac OS X 13_2_1",
	"Macintosh; Intel Mac OS X 13_3",
	"Macintosh; Intel Mac OS X 13_3_1",

	// Windows
	"Windows NT 10.0; Win64; x64",
	"Windows NT 5.1",
	"Windows NT 6.1; WOW64",
	"Windows NT 6.1; Win64; x64",

	// Linux
	"X11; Linux x86_64",
}

// Generates Firefox Browser User-Agent (Desktop)
//
// -> "Mozilla/5.0 (Macintosh; Intel Mac OS X 10.15; rv:87.0) Gecko/20100101 Firefox/87.0"
// export
func genFirefoxUA() string {
	version := ffVersions[rand.Intn(len(ffVersions))]
	os := osStrings[rand.Intn(len(osStrings))]
	return fmt.Sprintf("Mozilla/5.0 (%s; rv:%.1f) Gecko/20100101 Firefox/%.1f", os, version, version)
}

// Generates Chrome Browser User-Agent (Desktop)
//
// -> "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/90.0.4430.72 Safari/537.36"
// export
func genChromeUA() string {
	version := chromeVersions[rand.Intn(len(chromeVersions))]
	os := osStrings[rand.Intn(len(osStrings))]
	return fmt.Sprintf("Mozilla/5.0 (%s) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/%s Safari/537.36", os, version)
}

// Generates Microsoft Edge User-Agent (Desktop)
//
// -> "User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/90.0.4430.72 Safari/537.36 Edg/90.0.818.39"
// export
func genEdgeUA() string {
	version := edgeVersions[rand.Intn(len(edgeVersions))]
	chromeVersion := strings.Split(version, ",")[0]
	edgeVersion := strings.Split(version, ",")[1]
	os := osStrings[rand.Intn(len(osStrings))]
	return fmt.Sprintf("Mozilla/5.0 (%s) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/%s Safari/537.36 Edg/%s", os, chromeVersion, edgeVersion)
}

// Generates Opera Browser User-Agent (Desktop)
//
// -> "Mozilla/5.0 (Macintosh; Intel Mac OS X 13_3_1) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/112.0.0.0 Safari/537.36 OPR/98.0.4759.3"
// export
func genOperaUA() string {
	version := operaVersions[rand.Intn(len(operaVersions))]
	chromeVersion := strings.Split(version, ",")[0]
	operaVersion := strings.Split(version, ",")[1]
	os := osStrings[rand.Intn(len(osStrings))]
	return fmt.Sprintf("Mozilla/5.0 (%s) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/%s Safari/537.36 OPR/%s", os, chromeVersion, operaVersion)
}

// Generates Pixel 7 Browser User-Agent (Mobile)
//
// -> Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/112.0.0.0 Mobile Safari/537.36
// export
func genMobilePixel7UA() string {
	android := pixel7AndroidVersions[rand.Intn(len(pixel7AndroidVersions))]
	chrome := chromeVersions[rand.Intn(len(chromeVersions))]
	return fmt.Sprintf("Mozilla/5.0 (Linux; Android %s; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/%s Safari/537.36", android, chrome)
}

// Generates Pixel 6 Browser User-Agent (Mobile)
//
// -> "Mozilla/5.0 (Linux; Android 13; Pixel 6) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/112.0.0.0 Mobile Safari/537.36"
// export
func genMobilePixel6UA() string {
	android := pixel6AndroidVersions[rand.Intn(len(pixel6AndroidVersions))]
	chrome := chromeVersions[rand.Intn(len(chromeVersions))]
	return fmt.Sprintf("Mozilla/5.0 (Linux; Android %s; Pixel 6) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/%s Safari/537.36", android, chrome)
}

// Generates Pixel 5 Browser User-Agent (Mobile)
//
// -> "Mozilla/5.0 (Linux; Android 13; Pixel 5) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/112.0.0.0 Mobile Safari/537.36"
// export
func genMobilePixel5UA() string {
	android := pixel5AndroidVersions[rand.Intn(len(pixel5AndroidVersions))]
	chrome := chromeVersions[rand.Intn(len(chromeVersions))]
	return fmt.Sprintf("Mozilla/5.0 (Linux; Android %s; Pixel 5) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/%s Safari/537.36", android, chrome)
}

// Generates Pixel 4 Browser User-Agent (Mobile)
//
// -> "Mozilla/5.0 (Linux; Android 13; Pixel 4) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/112.0.0.0 Mobile Safari/537.36"
// export
func genMobilePixel4UA() string {
	android := pixel4AndroidVersions[rand.Intn(len(pixel4AndroidVersions))]
	chrome := chromeVersions[rand.Intn(len(chromeVersions))]
	return fmt.Sprintf("Mozilla/5.0 (Linux; Android %s; Pixel 4) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/%s Safari/537.36", android, chrome)
}

// Generates Nexus 10 Browser User-Agent (Mobile)
//
// -> "Mozilla/5.0 (Linux; Android 5.1.1; Nexus 10 Build/LMY48T) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/49.0.2623.91 Safari/537.36"
// export
func genMobileNexus10UA() string {
	build := nexus10Builds[rand.Intn(len(nexus10Builds))]
	android := nexus10AndroidVersions[rand.Intn(len(nexus10AndroidVersions))]
	chrome := chromeVersions[rand.Intn(len(chromeVersions))]
	return fmt.Sprintf("Mozilla/5.0 (Linux; Android %s; Nexus 10 Build/%s) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/%s Safari/537.36", android, build, chrome)
}

// HttpPostForm 参数为请求地址 (Form 数据 map[string]string, HttpReq, 超时时间)
// HttpPostForm(url)、HttpPostForm(url, timeout)、HttpPostForm(url, posts)、HttpPostForm(url, posts, timeout)、HttpPostForm(url, posts, HttpReq)、HttpPostForm(url, posts, HttpReq, timeout)
// 返回 body, 错误信息
// export
func HttpPostForm(urlStr string, args ...any) ([]byte, error) {
	l := len(args)

	switch l {
	case 0:
		return HttpPostFormDo(urlStr, nil, nil, 0)
	case 1:
		switch v := args[0].(type) {
		case int:
			timeout := ToInt(args[0])
			return HttpPostFormDo(urlStr, nil, nil, timeout)
		case map[string]string:
			return HttpPostFormDo(urlStr, v, nil, 0)
		}
	case 2:
		switch v := args[0].(type) {
		case map[string]string:
			switch h := args[1].(type) {
			case int:
				timeout := ToInt(args[1])
				return HttpPostFormDo(urlStr, v, nil, timeout)
			case *HttpReq:
				return HttpPostFormDo(urlStr, v, h, 0)
			}
		}
	case 3:
		switch v := args[0].(type) {
		case map[string]string:
			switch h := args[1].(type) {
			case *HttpReq:
				timeout := ToInt(args[2])
				return HttpPostFormDo(urlStr, v, h, timeout)
			}
		}
	}

	return nil, errors.New("http post Form params error")
}

// HttpPostJson 参数为请求地址 (Json 数据 string, HttpReq, 超时时间)
// HttpPostJson(url)、HttpPostJson(url, timeout)、HttpPostJson(url, json)、HttpPost(url, json, timeout)、HttpPost(url, json, HttpReq)、HttpPost(url, json, HttpReq, timeout)
// 返回 body, 错误信息
// export
func HttpPostJson(urlStr string, args ...any) ([]byte, error) {
	l := len(args)
	switch l {
	case 0:
		return HttpPostJsonDo(urlStr, "{}", nil, 0)
	case 1:
		switch v := args[0].(type) {
		case int:
			timeout := ToInt(args[0])
			return HttpPostJsonDo(urlStr, "{}", nil, timeout)
		case string:
			return HttpPostJsonDo(urlStr, v, nil, 0)
		}
	case 2:
		switch v := args[0].(type) {
		case string:
			switch h := args[1].(type) {
			case int:
				timeout := ToInt(args[1])
				return HttpPostJsonDo(urlStr, v, nil, timeout)
			case *HttpReq:
				return HttpPostJsonDo(urlStr, v, h, 0)
			}
		}
	case 3:
		switch v := args[0].(type) {
		case string:
			switch h := args[1].(type) {
			case *HttpReq:
				timeout := ToInt(args[2])
				return HttpPostJsonDo(urlStr, v, h, timeout)
			}
		}
	}

	return nil, errors.New("http post json params error")
}

// HttpPut 参数为请求地址 (body io.Reader, HttpReq, 超时时间)
// HttpPut(url)、HttpPut(url, timeout)、HttpPut(url, body)、HttpPut(url, body, timeout)、HttpPut(url, body, HttpReq)、HttpPut(url, body, HttpReq, timeout)
// 返回 body, 错误信息

// export
func CreateHTML(template string, values []interface{}) string {
	templatem := fmt.Sprintf(template, values...)
	return templatem
}

// export
func GinRouter() *gin.Engine {
	gin.SetMode(gin.ReleaseMode) // Modo Release para despliegue
	r := gin.Default()

	r.Use(cors.New(cors.Config{
		AllowOrigins:     []string{"*"}, // Permitir todos los orígenes
		AllowMethods:     []string{"GET", "POST", "PUT", "DELETE"},
		AllowHeaders:     []string{"Origin", "Content-Type"},
		AllowCredentials: true,
	}))

	return r
}

// IsNumber 判断字符串是否全部为数字
// export
func IsNumber(str string) bool {
	if len(str) == 0 {
		return false
	}

	for _, r := range str {
		if !unicode.IsNumber(r) {
			return false
		}
	}

	return true
}

// IsUtf8 判断是否为 UTF-8 编码
// export
func IsUtf8(p []byte) bool {
	return utf8.Valid(p)
}

// IsASCIILetter 判断字符串是否全部为ASCII的字母
// export
func IsASCIILetter(str string) bool {
	if len(str) == 0 {
		return false
	}

	runeList := []rune(str)
	for _, r := range runeList {
		if !((65 <= r && r <= 90) || (97 <= r && r <= 122)) {
			return false
		}
	}

	return true
}

// IsLetter 判断字符串是否全部为字母
// export
func IsLetter(str string) bool {
	if len(str) == 0 {
		return false
	}

	for _, r := range str {
		if !unicode.IsLetter(r) {
			return false
		}
	}

	return true
}

// IsASCII 判断字符串是否全部 ASCII
// export
func IsASCII(s string) bool {
	for i := 0; i < len(s); i++ {
		if s[i] > unicode.MaxASCII {
			return false
		}
	}
	return true
}

// IsEmail 验证 Email 是否合法
// export
func IsEmail(str string) bool {
	if !Blank(str) {
		return RegexEmailPattern.MatchString(str)
	}

	return false
}

// IsExist 文件或目录是否存在
// export
func IsExist(path string) bool {
	_, err := os.Stat(path)
	if err == nil {
		return true
	}
	if errors.Is(err, os.ErrNotExist) {
		return false
	}

	return false
}

// IsDir 是否是目录
// export
func IsDir(path string) bool {
	s, err := os.Stat(path)
	if err != nil {
		return false
	}

	return s.IsDir()
}

// IsIp 是否是有效的 IP
// export
func IsIp(ipStr string) bool {
	ip := net.ParseIP(ipStr)
	return ip != nil
}

// IsIpV4 是否是有效的 IpV4
// export
func IsIpV4(ipStr string) bool {
	ip := net.ParseIP(ipStr)
	if ip == nil {
		return false
	}
	return strings.Contains(ipStr, ".")
}

// IsIpV6 是否是有效的 IpV6
// export
func IsIpV6(ipStr string) bool {
	ip := net.ParseIP(ipStr)
	if ip == nil {
		return false
	}
	return strings.Contains(ipStr, ":")
}

// MapKeys 返回map的键切片
// export
func MapKeys[K comparable, V any](m map[K]V) []K {
	keys := make([]K, 0, len(m))

	for k := range m {
		keys = append(keys, k)
	}

	return keys
}

// MapValues 返回map的值切片
// export
func MapValues[K comparable, V any](m map[K]V) []V {
	values := make([]V, 0, len(m))

	for _, v := range m {
		values = append(values, v)
	}

	return values
}

// MapMerge 合并多个map, 如果有相同的键, 则后者会覆盖前者
// export
func MapMerge[K comparable, V any](maps ...map[K]V) map[K]V {
	res := make(map[K]V, 0)

	for _, m := range maps {
		for k, v := range m {
			res[k] = v
		}
	}

	return res
}

// export
func MapIntefaceToMapString(input map[string]interface{}) (map[string]string, error) {
	output := make(map[string]string)

	for key, value := range input {
		var strValue string
		switch v := value.(type) {
		case string:
			strValue = v
		case int:
			strValue = strconv.Itoa(v)
		case float64:
			strValue = strconv.FormatFloat(v, 'f', -1, 64)
		case bool:
			strValue = strconv.FormatBool(v)
		default:
			return nil, errors.New("tipo no soportado para la clave: " + key)
		}

		output[key] = strValue
	}

	return output, nil
}

// export
func MapStringToMapInterface(input map[string]string) (map[string]interface{}, error) {
	output := make(map[string]interface{})

	for key, value := range input {
		// Intentar convertir a int
		if intValue, err := strconv.Atoi(value); err == nil {
			output[key] = intValue
			continue
		}

		// Intentar convertir a float64
		if floatValue, err := strconv.ParseFloat(value, 64); err == nil {
			output[key] = floatValue
			continue
		}

		// Intentar convertir a bool
		if boolValue, err := strconv.ParseBool(value); err == nil {
			output[key] = boolValue
			continue
		}

		// Si no se puede convertir, mantenerlo como string
		output[key] = value
	}

	return output, nil
}

type KeyValue struct {
	Key   string
	Value interface{}
	Type  string
}

// export
func ConvertToTypedStructure(input map[string]string) ([]KeyValue, error) {
	var output []KeyValue

	for key, value := range input {
		var typedValue interface{}
		var dataType string

		// Intentar convertir a int
		if intValue, err := strconv.Atoi(value); err == nil {
			typedValue = intValue
			dataType = "int"
		} else if floatValue, err := strconv.ParseFloat(value, 64); err == nil {
			typedValue = floatValue
			dataType = "float64"
		} else if boolValue, err := strconv.ParseBool(value); err == nil {
			typedValue = boolValue
			dataType = "bool"
		} else {
			typedValue = value
			dataType = "string"
		}

		output = append(output, KeyValue{Key: key, Value: typedValue, Type: dataType})
	}

	return output, nil
}

// export
func MapSlicesToMap(datosRecibidos map[string][]string) map[string]string {
	recivedData := make(map[string]string)
	for key, values := range datosRecibidos {
		recivedData[key] = values[0] // Solo toma el primer valor
	}
	return recivedData
}

// Max 取 int 最大值
// export
func Max(a, b int) int {
	if a > b {
		return a
	}

	return b
}

// Min 取 int 最小值
// export
func Min(a, b int) int {
	if a < b {
		return a
	}

	return b
}

// MaxInt64 取 int64 最大值
// export
func MaxInt64(a, b int64) int64 {
	if a > b {
		return a
	}

	return b
}

// MinInt64 取 int64 最小值
// export
func MinInt64(a, b int64) int64 {
	if a < b {
		return a
	}

	return b
}

// MaxN 取 N 个数字的最大值
// export
func MaxN[T GenNumber](args ...T) T {
	max := args[0]
	for _, arg := range args {
		if arg > max {
			max = arg
		}
	}

	return max
}

// MinN 取 N 个数字的最小值
// export
func MinN[T GenNumber](args ...T) T {
	min := args[0]
	for _, arg := range args {
		if arg < min {
			min = arg
		}
	}

	return min
}

var (
	randomNew = rand.New(rand.NewSource(time.Now().UnixNano()))
)

// Random 返回随机数 `[0, MaxInt)`
// export
func Random() int {
	return randomNew.Intn(math.MaxInt)
}

// RandomInt 返回随机数 `[min, max)`
// export
func RandomInt(min, max int) int {
	if min > max {
		min, max = max, min
	}

	return randomNew.Intn(max-min) + min
}

// RandomInt64 返回随机数 `[min, max)`
// export
func RandomInt64(min, max int64) int64 {
	if min > max {
		min, max = max, min
	}

	return randomNew.Int63n(max-min) + min
}

// RandomString 返回指定长度的随机字符串, 包含字母和数字
// export
func RandomString(length int) string {
	return RandomPool(StringLetterAndNumber, length)
}

// RandomLetter 返回指定长度的随机字符串, 仅包含字母
// export
func RandomLetter(length int) string {
	return RandomPool(StringLetter, length)
}

// RandomNumber 返回指定长度的随机字符串, 仅包含数字
// export
func RandomNumber(length int) string {
	return RandomPool(StringNumber, length)
}

// RandomPool 从提供的字符串池中返回指定长度的随机字符串
// export
func RandomPool(pool string, length int) string {
	if length <= 0 {
		return ""
	}

	var chars = Bytes(pool)
	var result []byte

	for i := 0; i < length; i++ {
		c := chars[RandomInt(0, len(chars))]
		result = append(result, c)
	}

	return String(result)
}

const (
	RegexLetter       string = "^[a-zA-Z]+$"
	RegexLetterNumber string = "^[a-zA-Z0-9]+$"
	RegexNumber       string = "^[0-9]+$"
	RegexChinese      string = "^[\u4e00-\u9fa5]+$"
	RegexEmail        string = "^(?:(?:(?:(?:[a-zA-Z]|\\d|[!#\\$%&'\\*\\+\\-\\/=\\?\\^_`{\\|}~]|[\\x{00A0}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFEF}])+(?:\\.([a-zA-Z]|\\d|[!#\\$%&'\\*\\+\\-\\/=\\?\\^_`{\\|}~]|[\\x{00A0}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFEF}])+)*)|(?:(?:\\x22)(?:(?:(?:(?:\\x20|\\x09)*(?:\\x0d\\x0a))?(?:\\x20|\\x09)+)?(?:(?:[\\x01-\\x08\\x0b\\x0c\\x0e-\\x1f\\x7f]|\\x21|[\\x23-\\x5b]|[\\x5d-\\x7e]|[\\x{00A0}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFEF}])|(?:(?:[\\x01-\\x09\\x0b\\x0c\\x0d-\\x7f]|[\\x{00A0}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFEF}]))))*(?:(?:(?:\\x20|\\x09)*(?:\\x0d\\x0a))?(\\x20|\\x09)+)?(?:\\x22))))@(?:(?:(?:[a-zA-Z]|\\d|[\\x{00A0}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFEF}])|(?:(?:[a-zA-Z]|\\d|[\\x{00A0}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFEF}])(?:[a-zA-Z]|\\d|-|\\.|~|[\\x{00A0}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFEF}])*(?:[a-zA-Z]|\\d|[\\x{00A0}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFEF}])))\\.)+(?:(?:[a-zA-Z]|[\\x{00A0}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFEF}])|(?:(?:[a-zA-Z]|[\\x{00A0}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFEF}])(?:[a-zA-Z]|\\d|-|\\.|~|[\\x{00A0}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFEF}])*(?:[a-zA-Z]|[\\x{00A0}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFEF}])))\\.?$"
	RegexDateTime     string = "(((\\d{4})[-/年.])(0[1-9]|1[0-2]|[1-9])[-/月.](0[1-9]|[1-2][0-9]|3[0-1]|[1-9])[日Tt]?[ ]{0,3}(([0-9]|[0-1][0-9]|2[0-3]|[1-9])[:点时]([0-5][0-9]|[0-9])[:分]?(([0-5][0-9]|[0-9])[秒]?)?((\\.\\d{3})?)(z|Z|[\\+-]\\d{2}[:]?\\d{2})?)?)"
)

var (
	RegexEmailPattern    = regexp.MustCompile(RegexEmail)
	RegexDateTimePattern = regexp.MustCompile(RegexDateTime)
)

// Matches 判断字符串是否匹配指定的正则表达式
// export
func Matches(str, pattern string) bool {
	match, _ := regexp.MatchString(pattern, str)

	return match
}

type result struct {
	// date
	y *int
	m *int
	d *int
	// time
	h *int
	i *int
	s *int
	f *int

	// relative shifts
	ry int
	rm int
	rd int
	rh int
	ri int
	rs int
	rf int

	// weekday related shifts
	weekday         *int
	weekdayBehavior int

	// first or last day of month
	// 0 none, 1 first, -1 last
	firstOrLastDayOfMonth int

	// timezone correction in minutes
	z *int

	// counters
	dates int
	times int
	zones int
}

// export
func (r *result) ymd(y, m, d int) error {
	if r.dates > 0 {
		return fmt.Errorf("strtotime: The string contains two conflicting date/months")
	}

	r.dates++
	r.y = pointer(y)
	r.m = pointer(m)
	r.d = pointer(d)
	return nil
}

// export
func (r *result) time(h, i, s, f int) error {
	if r.times > 0 {
		return fmt.Errorf("strtotime: The string contains two conflicting hours")
	}

	r.times++
	r.h = &h
	r.i = &i
	r.s = &s
	r.f = &f

	return nil
}

// export
func (r *result) resetTime() error {
	r.h = pointer(0)
	r.i = pointer(0)
	r.s = pointer(0)
	r.f = pointer(0)
	r.times = 0

	return nil
}

// export
func (r *result) zone(minutes int) error {
	if r.zones > 0 {
		return fmt.Errorf("strtotime: The string contains two conflicting time zones")

	}
	r.zones++
	r.z = pointer(minutes)
	return nil
}

// export
func (r *result) toDate(re int64) time.Time {

	relativeTo := time.Unix(re, 0).Local()

	if r.dates > 0 && r.times <= 0 {
		r.h = pointer(0)
		r.i = pointer(0)
		r.s = pointer(0)
		r.f = pointer(0)
	}

	// fill holes
	if r.y == nil {
		y := relativeTo.Year()
		r.y = &y
	}

	if r.m == nil {
		m := lookupMonth(relativeTo.Month().String())
		r.m = &m
	}

	if r.d == nil {
		d := relativeTo.Day()
		r.d = &d
	}

	if r.h == nil {
		h := relativeTo.Hour()
		r.h = &h
	}

	if r.i == nil {
		i := relativeTo.Minute()
		r.i = &i
	}

	if r.s == nil {
		s := relativeTo.Second()
		r.s = &s
	}

	if r.f == nil {
		f := relativeTo.Nanosecond() / 1000000
		r.f = &f
	}

	// adjust special early
	switch r.firstOrLastDayOfMonth {
	case 1:
		*r.d = 1
		//break
	case -1:
		*r.d = 0
		//break
	}

	if r.weekday != nil {

		var dow = lookupWeekday(relativeTo.Weekday().String(), 1)

		if r.weekdayBehavior == 2 {
			// To make "r week" work, where the current day of week is a "sunday"
			if dow == 0 && *r.weekday != 0 {
				*r.weekday = -6
			}

			// To make "sunday r week" work, where the current day of week is not a "sunday"
			if *r.weekday == 0 && dow != 0 {
				*r.weekday = 7
			}

			*r.d -= dow
			*r.d += *r.weekday
		} else {
			var diff = *r.weekday - dow

			// TODO: Fix this madness
			if (r.rd < 0 && diff < 0) || (r.rd >= 0 && diff <= -r.weekdayBehavior) {
				diff += 7
			}

			if *r.weekday >= 0 {
				*r.d += diff
			} else {
				// TODO: Fix this madness
				*r.d -= int(7 - (math.Abs(float64(*r.weekday)) - float64(dow)))
			}

			r.weekday = nil
		}
	}

	// adjust relative
	*r.y += r.ry
	*r.m += r.rm
	*r.d += r.rd

	// 月份如果大于 11, 需要加年份
	if *r.m > 11 {
		*r.y += (*r.m + 1) / 12
		*r.m %= 12
	} else if *r.m < 0 {
		*r.y += int(math.Floor(float64(*r.m) / 12.0))
		*r.m = ((*r.m % 12) + 12) % 12
	}

	*r.h += r.rh
	*r.i += r.ri
	*r.s += r.rs
	*r.f += r.rf

	r.ry = 0
	r.rm = 0
	r.rd = 0
	r.rh = 0
	r.ri = 0
	r.rs = 0
	r.rf = 0

	// note: this is done twice in PHP
	// early when processing special relatives
	// and late
	// todo: check if the logic can be reduced
	// to just one time action
	switch r.firstOrLastDayOfMonth {
	case 1:
		*r.d = 1
		//break
	case -1:
		m := lookupNumberToMonth(*r.m)
		firstOfMonth := time.Date(*r.y, m, 1, 0, 0, 0, 0, time.Local)
		lastOfMonth := firstOfMonth.AddDate(0, 1, -1)
		_, _, *r.d = lastOfMonth.Date()
		//break
	}

	// TODO: process and adjust timezone
	if r.z != nil {
		*r.i += *r.z
	}

	return time.Date(*r.y, lookupNumberToMonth(*r.m), *r.d, *r.h, *r.i, *r.s, *r.f, time.Local)
}

// export
func Similarity(a, b string) float64 {
	len1 := len([]rune(a))
	len2 := len([]rune(b))

	if len1 == 0 && len2 == 0 {
		return 1
	}

	lcs := float64(LongestCommonSubString(a, b))
	max := float64(Max(len1, len2))

	return lcs / max
}

// SimilarityText 计算两个字符串移除特殊符号后的相似度
// export
func SimilarityText(a, b string) float64 {
	a = RemoveSign(a)
	b = RemoveSign(b)

	return Similarity(a, b)
}

// LongestCommonSubString 计算两个字符串最大公共子串长度
// export
func LongestCommonSubString(x, y string) int {
	rm := []rune(x)
	rn := []rune(y)

	m := len(rm)
	n := len(rn)

	if m == 0 || n == 0 {
		return 0
	}

	// 初始化二维数组
	var opt = make([][]int, m+1)
	for i := 0; i < m+1; i++ {
		opt[i] = make([]int, n+1)
	}

	for i := m - 1; i >= 0; i-- {
		for j := n - 1; j >= 0; j-- {
			if rm[i] == rn[j] {
				opt[i][j] = opt[i+1][j+1] + 1
			} else {
				opt[i][j] = Max(opt[i+1][j], opt[i][j+1])
			}
		}
	}

	return opt[0][0]
}

// IntsToStrings int 切片转换为字符串切片
// export
func IntsToStrings(slice []int) []string {
	if len(slice) == 0 {
		return []string{}
	}
	var str []string
	for _, v := range slice {
		str = append(str, strconv.Itoa(v))
	}

	return str
}

// StringsToInts 字符串切片转换为 int 切片
// export
func StringsToInts(slice []string) []int {
	if len(slice) == 0 {
		return []int{}
	}
	var ints []int
	for _, v := range slice {
		if i, err := strconv.Atoi(v); err == nil {
			ints = append(ints, i)
		}
	}

	return ints
}

// SliceContains 判断整型和字符串是否在切片中
// export
func SliceContains[T comparable](slice []T, v T) bool {
	if len(slice) == 0 {
		return false
	}

	for _, s := range slice {
		if s == v {
			return true
		}
	}

	return false
}

// SliceUnique 对数值和字符串切片进行去重(会改变元素的顺序)
// export
func SliceUnique[T comparable](slice []T) []T {
	if len(slice) == 0 {
		return slice
	}
	m := make(map[T]bool)
	for i := range slice {
		m[slice[i]] = true
	}

	slice = slice[:0]
	for k := range m {
		slice = append(slice, k)
	}

	return slice
}

// SliceSplit 对数值和字符串切片按照指定长度进行分割
// export
func SliceSplit[T comparable](slice []T, size int) [][]T {
	var res [][]T

	if len(slice) == 0 || size <= 0 {
		return res
	}

	length := len(slice)
	if size == 1 || size >= length {
		for _, v := range slice {
			var tmp []T
			tmp = append(tmp, v)
			res = append(res, tmp)
		}
		return res
	}

	// divide slice equally
	divideNum := length/size + 1
	for i := 0; i < divideNum; i++ {
		if i == divideNum-1 {
			if len(slice[i*size:]) > 0 {
				res = append(res, slice[i*size:])
			}
		} else {
			res = append(res, slice[i*size:(i+1)*size])
		}
	}

	return res
}

// SliceIndex 对数值和字符串切片按照指定值进行查找
// export
func SliceIndex[T comparable](slice []T, v T) int {
	for i, s := range slice {
		if s == v {
			return i
		}
	}

	return -1
}

// SliceLastIndex 对数值和字符串切片按照指定值进行查找, 返回最后一个匹配的索引
// export
func SliceLastIndex[T comparable](slice []T, v T) int {
	for i := len(slice) - 1; i >= 0; i-- {
		if slice[i] == v {
			return i
		}
	}

	return -1
}

// SliceRemove 移除数值和字符串切片中的指定值
// export
func SliceRemove[T comparable](slice []T, v T) []T {
	if len(slice) == 0 {
		return slice
	}

	var res []T
	for _, s := range slice {
		if s != v {
			res = append(res, s)
		}
	}

	return res
}

// SliceRemoveBlank 移除字符串切片中的空值
// export
func SliceRemoveBlank(slice []string) []string {
	if len(slice) == 0 {
		return slice
	}

	var res []string
	for _, s := range slice {
		str := strings.TrimSpace(s)
		if len(str) > 0 {
			res = append(res, s)
		}
	}

	return res
}

// SliceTrim 对字符串切片进行 Trim, 并自动忽略空值
// export
func SliceTrim(slice []string) []string {
	if len(slice) == 0 {
		return slice
	}

	var res []string
	for _, s := range slice {
		str := strings.TrimSpace(s)
		if len(str) > 0 {
			res = append(res, str)
		}
	}

	return res
}

// SliceConcat 合并多个切片, 非去重, 非原始切片
// export
func SliceConcat[T any](slice []T, values ...[]T) []T {
	result := append([]T{}, slice...)

	for _, v := range values {
		result = append(result, v...)
	}

	return result
}

// SliceEqual 切片是否相等: 长度相同且所有元素的顺序和值相等
// export
func SliceEqual[T comparable](slice1, slice2 []T) bool {
	if len(slice1) != len(slice2) {
		return false
	}

	for i := range slice1 {
		if slice1[i] != slice2[i] {
			return false
		}
	}

	return true
}

// SliceEvery 切片中的所有元素都满足函数，则返回 true
// export
func SliceEvery[T any](slice []T, predicate func(index int, item T) bool) bool {
	var currentLength int

	for i, v := range slice {
		if predicate(i, v) {
			currentLength++
		}
	}

	return currentLength == len(slice)
}

// SliceNone 切片中的所有元素都不满足函数，则返回 true
// export
func SliceNone[T any](slice []T, predicate func(index int, item T) bool) bool {
	var currentLength int

	for i, v := range slice {
		if !predicate(i, v) {
			currentLength++
		}
	}

	return currentLength == len(slice)
}

// SliceSome 切片中有一个元素满足函数，就返回true
// export
func SliceSome[T any](slice []T, predicate func(index int, item T) bool) bool {
	for i, v := range slice {
		if predicate(i, v) {
			return true
		}
	}

	return false
}

// SliceFilter 筛选出切片中满足函数的所有元素
// export
func SliceFilter[T any](slice []T, predicate func(index int, item T) bool) []T {
	result := make([]T, 0)

	for i, v := range slice {
		if predicate(i, v) {
			result = append(result, v)
		}
	}

	return result
}

// SliceForEach 切片中所有元素都执行函数
// export
func SliceForEach[T any](slice []T, iteratee func(index int, item T)) {
	for i, v := range slice {
		iteratee(i, v)
	}
}

// SliceMap 切片中所有元素都执行函数, 有返回值
// export
func SliceMap[T any, U any](slice []T, iteratee func(index int, item T) U) []U {
	result := make([]U, len(slice), cap(slice))

	for i, v := range slice {
		result[i] = iteratee(i, v)
	}

	return result
}

// SliceReduce 处理所有切片中元素得到结果
// export
func SliceReduce[T any](slice []T, iteratee func(index int, result, item T) T, initial T) T {
	if len(slice) == 0 {
		return initial
	}

	result := iteratee(0, initial, slice[0])

	tmp := make([]T, 2)
	for i := 1; i < len(slice); i++ {
		tmp[0] = result
		tmp[1] = slice[i]
		result = iteratee(i, tmp[0], tmp[1])
	}

	return result
}

// SliceReplace 返回切片的副本，前n个元素替换为新的
// export
func SliceReplace[T comparable](slice []T, old T, new T, n int) []T {
	result := make([]T, len(slice))
	copy(result, slice)

	for i := range result {
		if result[i] == old && n != 0 {
			result[i] = new
			n--
		}
	}

	return result
}

// SliceReplaceAll 返回切片的副本，所有匹配到的元素都替换为新的
// export
func SliceReplaceAll[T comparable](slice []T, old T, new T) []T {
	return SliceReplace(slice, old, new, -1)
}

// SliceUnion 顺序合并且去重
// export
func SliceUnion[T comparable](slices ...[]T) []T {
	var result []T
	contain := map[T]struct{}{}

	for _, slice := range slices {
		for _, item := range slice {
			if _, ok := contain[item]; !ok {
				contain[item] = struct{}{}
				result = append(result, item)
			}
		}
	}

	return result
}

// SliceUnionBy 顺序合并且去重, 支持自定义函数
// export
func SliceUnionBy[T any, V comparable](predicate func(item T) V, slices ...[]T) []T {
	var result []T
	contain := map[V]struct{}{}

	for _, slice := range slices {
		for _, item := range slice {
			val := predicate(item)
			if _, ok := contain[val]; !ok {
				contain[val] = struct{}{}
				result = append(result, item)
			}
		}
	}

	return result
}

// SliceIntersection 切片交集且去重(顺序不能保证)
// export
func SliceIntersection[T comparable](slices ...[]T) []T {
	if len(slices) == 0 {
		return []T{}
	}
	if len(slices) == 1 {
		return SliceUnique(slices[0])
	}

	reducer := func(sliceA, sliceB []T) []T {
		hashMap := make(map[T]int)
		for _, val := range sliceA {
			hashMap[val] = 1
		}

		out := make([]T, 0)
		for _, val := range sliceB {
			if v, ok := hashMap[val]; v == 1 && ok {
				out = append(out, val)
				hashMap[val]++
			}
		}
		return out
	}

	result := reducer(slices[0], slices[1])

	reduceSlice := make([][]T, 2)
	for i := 2; i < len(slices); i++ {
		reduceSlice[0] = result
		reduceSlice[1] = slices[i]
		result = reducer(reduceSlice[0], reduceSlice[1])
	}

	return result
}

// sliceValue 返回切片的反射类型
// export
func sliceValue(slice any) reflect.Value {
	v := reflect.ValueOf(slice)
	if v.Kind() != reflect.Slice {
		panic(fmt.Sprintf("Invalid slice type, value of type %T", slice))
	}
	return v
}

// SliceSortBy 根据字段排序(field的大小写应该和字段保持一致)
// export
func SliceSortBy(slice any, field string, sortType ...string) error {
	sv := sliceValue(slice)
	t := sv.Type().Elem()

	if t.Kind() == reflect.Ptr {
		t = t.Elem()
	}
	if t.Kind() != reflect.Struct {
		return fmt.Errorf("data type %T not support, shuld be struct or pointer to struct", slice)
	}

	// Find the field.
	sf, ok := t.FieldByName(field)
	if !ok {
		return fmt.Errorf("field name %s not found", field)
	}

	// Create a less function based on the field's kind.
	var compare func(a, b reflect.Value) bool
	switch sf.Type.Kind() {
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		if len(sortType) > 0 && sortType[0] == "desc" {
			compare = func(a, b reflect.Value) bool { return a.Int() > b.Int() }
		} else {
			compare = func(a, b reflect.Value) bool { return a.Int() < b.Int() }
		}
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		if len(sortType) > 0 && sortType[0] == "desc" {
			compare = func(a, b reflect.Value) bool { return a.Uint() > b.Uint() }
		} else {
			compare = func(a, b reflect.Value) bool { return a.Uint() < b.Uint() }
		}
	case reflect.Float32, reflect.Float64:
		if len(sortType) > 0 && sortType[0] == "desc" {
			compare = func(a, b reflect.Value) bool { return a.Float() > b.Float() }
		} else {
			compare = func(a, b reflect.Value) bool { return a.Float() < b.Float() }
		}
	case reflect.String:
		if len(sortType) > 0 && sortType[0] == "desc" {
			compare = func(a, b reflect.Value) bool { return a.String() > b.String() }
		} else {
			compare = func(a, b reflect.Value) bool { return a.String() < b.String() }
		}
	case reflect.Bool:
		if len(sortType) > 0 && sortType[0] == "desc" {
			compare = func(a, b reflect.Value) bool { return a.Bool() && !b.Bool() }
		} else {
			compare = func(a, b reflect.Value) bool { return !a.Bool() && b.Bool() }
		}
	default:
		return fmt.Errorf("field type %s not supported", sf.Type)
	}

	sort.Slice(slice, func(i, j int) bool {
		a := sv.Index(i)
		b := sv.Index(j)
		if t.Kind() == reflect.Ptr {
			a = a.Elem()
			b = b.Elem()
		}
		a = a.FieldByIndex(sf.Index)
		b = b.FieldByIndex(sf.Index)
		return compare(a, b)
	})

	return nil
}

// SliceColumn 返回所有行的某一列
// export
func SliceColumn[T, V any](slice []T, key any) []V {
	values := make([]V, len(slice))
	switch reflect.TypeOf(slice).Elem().Kind() {
	case reflect.Slice, reflect.Array:
		for i, v := range slice {
			values[i] = reflect.ValueOf(v).Index(int(reflect.ValueOf(key).Int())).Interface().(V)
		}
	case reflect.Map:
		for i, v := range slice {
			values[i] = reflect.ValueOf(v).MapIndex(reflect.ValueOf(key)).Interface().(V)
		}
	case reflect.Struct:
		for i, v := range slice {
			values[i] = reflect.ValueOf(v).FieldByName(reflect.ValueOf(key).String()).Interface().(V)
		}
	}

	return values
}

// BlankAll 判断 Trim 后的字符串集, 是否全部为空白
// export
func BlankAll(strs ...string) bool {
	if len(strs) == 0 {
		return true
	}

	for _, v := range strs {
		if !Blank(v) {
			return false
		}
	}

	return true
}

// BlankAny 判断 Trim 后的字符串集, 是否任意一个包含空白
// export
func BlankAny(strs ...string) bool {
	if len(strs) == 0 {
		return true
	}

	for _, v := range strs {
		if Blank(v) {
			return true
		}
	}

	return false
}

// Blank 判断 Trim 后的字符串, 是否为空白
// export
func Blank(str string) bool {
	t := strings.TrimSpace(str)

	if t == "" {
		return true
	}

	return false
}

// HasPrefixCase 判断字符串是否以指定前缀开头, 忽略大小写
// export
func HasPrefixCase(str, prefix string) bool {
	return strings.HasPrefix(strings.ToLower(str), strings.ToLower(prefix))
}

// HasSuffixCase 判断字符串是否以指定后缀结尾, 忽略大小写
// export
func HasSuffixCase(str, prefix string) bool {
	return strings.HasSuffix(strings.ToLower(str), strings.ToLower(prefix))
}

// SplitTrim 分割字符串为字符串切片, 对分割后的值进行 Trim , 并自动忽略空值
// export
func SplitTrim(str, sep string) []string {
	if len(str) == 0 || len(sep) == 0 {
		return []string{}
	}

	// 如果没找到 sep, strings.Split 返回包含 str 长度 1 的切片
	ss := strings.Split(str, sep)
	if len(ss) <= 1 {
		return []string{str}
	}

	slices := make([]string, 0, len(ss))
	for i := range ss {
		s := strings.TrimSpace(ss[i])
		if len(s) > 0 {
			slices = append(slices, s)
		}
	}

	return slices
}

// SplitTrimToInts 分割字符串为 int 切片, 对分割后的值进行 Trim , 并自动忽略空值
// export
func SplitTrimToInts(str, sep string) []int {
	if len(str) == 0 || len(sep) == 0 {
		return []int{}
	}

	// 如果没找到 sep, strings.Split 返回包含 int(str) 长度 1 的切片
	ss := strings.Split(str, sep)
	if len(ss) <= 1 {
		s := ToInt(str)
		return []int{s}
	}

	slices := make([]int, 0, len(ss))
	for i := range ss {
		s := strings.TrimSpace(ss[i])
		if len(s) > 0 {
			if n, err := strconv.Atoi(s); err == nil {
				slices = append(slices, n)
			}
		}
	}

	return slices
}

// Contains 判断字符串是否包含指定的子串
// export
func Contains(str, substr string) bool {
	return strings.Contains(str, substr)
}

// ContainsCase 判断字符串是否包含指定的子串, 不区分大小写
// export
func ContainsCase(str, substr string) bool {
	return Contains(strings.ToLower(str), strings.ToLower(substr))
}

// ContainsAny 判断字符串是否包含任意一个指定的多个子串
// export
func ContainsAny(str string, substr ...string) bool {
	if len(str) == 0 || len(substr) == 0 {
		return false
	}

	for _, s := range substr {
		if Contains(str, s) {
			return true
		}
	}

	return false
}

// SnakeToCamel 蛇形转驼峰
// export
func SnakeToCamel(str string, bigCamel bool) string {
	if len(str) == 0 {
		return ""
	}

	if !Contains(str, UNDERSCORE) {
		return str
	}

	str = strings.ToLower(str)

	var sb strings.Builder
	sb.Grow(len(str))

	underscore := false
	for i, r := range str {
		if i == 0 {
			if bigCamel {
				sb.WriteRune(unicode.ToUpper(r))
			} else {
				sb.WriteRune(unicode.ToLower(r))
			}
		} else if r == '_' {
			if i < len(str) {
				underscore = true
			}
		} else if underscore {
			sb.WriteRune(unicode.ToUpper(r))
			underscore = false
		} else {
			sb.WriteRune(r)
		}
	}

	return sb.String()
}

// CamelToSnake 驼峰转蛇形
// export
func CamelToSnake(str string) string {
	if len(str) == 0 {
		return ""
	}

	var sb strings.Builder
	sb.Grow(len(str))

	for i, r := range str {
		if i == 0 {
			sb.WriteRune(unicode.ToLower(r))
		} else if unicode.IsUpper(r) {
			sb.WriteRune('_')
			sb.WriteRune(unicode.ToLower(r))
		} else {
			sb.WriteRune(r)
		}
	}

	return sb.String()
}

// PadLeft 左侧填充字符串到指定长度
// export
func PadLeft(str string, padStr string, padLen int) string {
	if len(str) >= padLen || padStr == "" {
		return str
	}

	return buildPadStr(str, padStr, padLen, true, false)
}

// PadRight 右侧填充字符串到指定长度
// export
func PadRight(str string, padStr string, padLen int) string {
	if len(str) >= padLen || padStr == "" {
		return str
	}

	return buildPadStr(str, padStr, padLen, false, true)
}

// PadBoth 两侧填充字符串到指定长度
// export
func PadBoth(str string, padStr string, padLen int) string {
	if len(str) >= padLen || padStr == "" {
		return str
	}

	return buildPadStr(str, padStr, padLen, true, true)
}

// Wrap 使用字符串包围原字符串
// export
func Wrap(str string, wrapStr string) string {
	if len(str) == 0 || wrapStr == "" {
		return str
	}
	var sb strings.Builder
	sb.WriteString(wrapStr)
	sb.WriteString(str)
	sb.WriteString(wrapStr)

	return sb.String()
}

// Unwrap 去除字符串包围, 非递归
// export
func Unwrap(str string, wrapStr string) string {
	if str == "" || wrapStr == "" {
		return str
	}

	firstIndex := strings.Index(str, wrapStr)
	lastIndex := strings.LastIndex(str, wrapStr)

	if firstIndex == 0 && lastIndex > 0 && lastIndex <= len(str)-1 {
		if len(wrapStr) <= lastIndex {
			str = str[len(wrapStr):lastIndex]
		}
	}

	return str
}

// buildPadStr
// export
func buildPadStr(str string, padStr string, padLen int, padLeft bool, padRight bool) string {
	if padLen < utf8.RuneCountInString(str) {
		return str
	}

	padLen -= utf8.RuneCountInString(str)

	targetLen := padLen

	targetLenLeft := targetLen
	targetLenRight := targetLen
	if padLeft && padRight {
		targetLenLeft = padLen / 2
		targetLenRight = padLen - targetLenLeft
	}

	strToRepeatLen := utf8.RuneCountInString(padStr)

	repeatTimes := int(math.Ceil(float64(targetLen) / float64(strToRepeatLen)))
	repeatedString := strings.Repeat(padStr, repeatTimes)

	leftSide := ""
	if padLeft {
		leftSide = repeatedString[0:targetLenLeft]
	}

	rightSide := ""
	if padRight {
		rightSide = repeatedString[0:targetLenRight]
	}

	return leftSide + str + rightSide
}

// Reverse 反转字符串
// export
func Reverse(str string) string {
	runes := []rune(str)
	for i, j := 0, len(runes)-1; i < j; i, j = i+1, j-1 {
		runes[i], runes[j] = runes[j], runes[i]
	}

	return string(runes)
}

// Remove 移除字符串中指定的字符串
// export
func Remove(str, remove string) string {
	if str == "" || remove == "" {
		return remove
	}

	return strings.Replace(str, remove, "", -1)
}

// RemovePrefix 左侧移除字符串中指定的字符串
// export
func RemovePrefix(str, prefix string) string {
	if str == "" || prefix == "" {
		return str
	}

	return strings.TrimPrefix(str, prefix)
}

// RemoveSuffix 右侧移除字符串中指定的字符串
// export
func RemoveSuffix(str string, suffix string) string {
	if str == "" || suffix == "" {
		return str
	}

	return strings.TrimSuffix(str, suffix)
}

// RemoveAny 移除字符串中指定的字符串集
// export
func RemoveAny(str string, removes ...string) string {
	if str == "" || len(removes) == 0 {
		return str
	}

	for _, rr := range removes {
		str = Remove(str, rr)
	}

	return str
}

// RemoveSign 将字符串的所有数据依次写成一行, 去除无意义字符串(标点符号、符号), 性能原因, 不使用 strings.NewReplacer
// export
func RemoveSign(str string) string {
	if strings.Contains(str, LF) {
		str = strings.ReplaceAll(str, LF, "")
	}

	if strings.Contains(str, CRLF) {
		str = strings.ReplaceAll(str, CRLF, "")
	}

	if strings.Contains(str, TAB) {
		str = strings.ReplaceAll(str, TAB, "")
	}

	if strings.Contains(str, SPACE) {
		str = strings.ReplaceAll(str, SPACE, "")
	}

	m := regexp.MustCompile(`[\pP\pS]`)

	return m.ReplaceAllString(str, "")
}

// RemoveLines 移除换行符, 换行符包括 \n \r\n, 性能原因, 不使用 strings.NewReplacer
// export
func RemoveLines(str string) string {
	if strings.Contains(str, LF) {
		str = strings.ReplaceAll(str, LF, "")
	}

	if strings.Contains(str, CRLF) {
		str = strings.ReplaceAll(str, CRLF, "")
	}

	return str
}

// SubString 字符串截取
// export
func SubString(str string, pos, length int) string {
	runes := []rune(str)
	max := len(runes)

	if pos < 0 || length <= 0 {
		return str
	}

	if pos > max {
		return ""
	}

	l := pos + length
	if l > max {
		l = max
	}

	return string(runes[pos:l])
}

// NormaliseSpace 规范化此字符串中的空白, 多个空格合并为一个空格, 所有空白字符例如换行符、制表符, 都转换为一个简单的空格。
// export
func NormaliseSpace(str string) string {
	str = strings.Join(strings.Fields(str), " ")

	return str
}

// NormaliseLine 规范化此字符串中的换行, 多个换行合并为一个换行
// export
func NormaliseLine(str string) string {
	lines := SplitTrim(str, LF)
	if len(lines) > 0 {
		str = strings.Join(lines, LF)
	}

	return str
}

// Template 模板渲染
// export
func Template(tpl string, data any) (string, error) {
	t := template.Must(template.New("").Parse(tpl))

	buf := new(bytes.Buffer)
	if err := t.Execute(buf, data); err != nil {
		return "", err
	}

	return String(buf.Bytes()), nil
}

// StrBefore 截取在字符首次出现时的位置之前的子字符串
// export
func StrBefore(s, char string) string {
	if s == "" || char == "" {
		return s
	}
	i := strings.Index(s, char)

	return s[0:i]
}

// StrBeforeLast 截取在字符最后出现时的位置之前的子字符串
// export
func StrBeforeLast(s, char string) string {
	if s == "" || char == "" {
		return s
	}
	i := strings.LastIndex(s, char)

	return s[0:i]
}

// StrAfter 截取在字符首次出现时的位置之后的子字符串
// export
func StrAfter(s, char string) string {
	if s == "" || char == "" {
		return s
	}
	i := strings.Index(s, char)

	return s[i+len(char):]
}

// StrAfterLast 截取在字符最后出现时的位置之后的子字符串
// export
func StrAfterLast(s, char string) string {
	if s == "" || char == "" {
		return s
	}
	i := strings.LastIndex(s, char)

	return s[i+len(char):]
}

// Parse takes an English string - such as "next Friday 3 pm" - and an int64 unix timestamp to compare it with.
// It returns the translated English text into an int64 unix timestamp, or an error if the input cannot be recognized.
// export
func Parse(s string, relativeTo int64) (int64, error) {

	if strings.Contains(s, "T") {

		DateTimeMatchers := []string{
			// 时分秒+时区偏移量 (最常用)
			"2006-01-02T15:04:05-07:00",
			"2006-01-02T15:04:05-0700",
			"2006-01-02T15:04:05Z",
			"2006-01-02T15:04:05z",
			"2006/01/02T15:04:05-07:00",
			"2006/01/02T15:04:05-0700",
			"2006/01/02T15:04:05Z",
			"2006/01/02T15:04:05z",

			// 1
			"2006-01-02T15:04:05-07:00:00",
			"2006-01-02T15:04:05-070000",
			"2006-01-02T15:04:05-07",
			"2006-01-02T15:04-07:00",
			"2006-01-02T15:04-0700",
			"2006-01-02T15:04-07:00:00",
			"2006-01-02T15:04-070000",
			"2006-01-02T15:04-07",

			// 2
			"2006/01/02T15:04:05-07:00:00",
			"2006/01/02T15:04:05-070000",
			"2006/01/02T15:04:05-07",
			"2006/01/02T15:04-07:00",
			"2006/01/02T15:04-0700",
			"2006/01/02T15:04-07:00:00",
			"2006/01/02T15:04-070000",
			"2006/01/02T15:04-07",

			// 3
			"2006-01-02T15:04Z",
			"2006-01-02T15:04z",

			// 4
			"2006/01/02T15:04Z",
			"2006/01/02T15:04z",
		}

		hour := getUtcHour(s)

		for _, layout := range DateTimeMatchers {

			secondoffset := int((time.Duration(hour) * time.Hour).Seconds())
			zoneLocal := time.FixedZone("zoneoffset", secondoffset)

			v, err := time.ParseInLocation(layout, s, zoneLocal)
			if err != nil {
				continue
			} else {
				return v.Unix(), nil
			}
		}
	}

	r := &result{}
	formats := formats()
	for {
		noMatch := true
		for _, format := range formats {

			re := regexp.MustCompile(format.regex)
			match := re.FindStringSubmatch(s)

			if len(match) <= 0 {
				continue
			}

			noMatch = false

			err := format.callback(r, match[1:]...)

			if err != nil {
				return 0, err
			}

			s = strings.TrimSpace(re.ReplaceAllString(s, ""))
			//break
		}

		if len(s) == 0 {
			return r.toDate(relativeTo).Unix(), nil
		}

		if noMatch {
			return 0, fmt.Errorf(`strtotime: Unrecognizable input: "%v"`, s)
		}
	}
}

// processMeridian converts 12 hour format type to 24 hour format
// export
func processMeridian(h int, m string) int {
	m = strings.ToLower(m)
	switch m {
	case "am":
		if h == 12 {
			h -= 12
		}
		//break
	case "pm":
		if h != 12 {
			h += 12
		}
		//break
	}

	return h
}

// processYear converts a year string such as "75" to a year, such as 1975
// export
func processYear(yearStr string) (int, error) {
	y, err := strconv.Atoi(yearStr)

	cutoffYear := 70 // Magic number. Anything before this will be in the 2000s. After, 1900s.

	if err != nil {
		return 0, err
	}

	if len(yearStr) >= 4 || y >= 100 {
		return y, nil
	}

	if y < cutoffYear {
		y += 2000
		return y, nil
	}

	if y >= cutoffYear {
		y += 1900
		return y, nil
	}

	return y, nil
}

// export
func lookupMonth(m string) int {
	monthMap := map[string]int{
		"jan":       0,
		"january":   0,
		"i":         0,
		"feb":       1,
		"february":  1,
		"ii":        1,
		"mar":       2,
		"march":     2,
		"iii":       2,
		"apr":       3,
		"april":     3,
		"iv":        3,
		"may":       4,
		"v":         4,
		"jun":       5,
		"june":      5,
		"vi":        5,
		"jul":       6,
		"july":      6,
		"vii":       6,
		"aug":       7,
		"august":    7,
		"viii":      7,
		"sep":       8,
		"sept":      8,
		"september": 8,
		"ix":        8,
		"oct":       9,
		"october":   9,
		"x":         9,
		"nov":       10,
		"november":  10,
		"xi":        10,
		"dec":       11,
		"december":  11,
		"xii":       11,
	}
	return monthMap[strings.ToLower(m)]
}

// export
func lookupNumberToMonth(m int) time.Month {
	monthMap := map[int]time.Month{
		0:  time.January,
		1:  time.February,
		2:  time.March,
		3:  time.April,
		4:  time.May,
		5:  time.June,
		6:  time.July,
		7:  time.August,
		8:  time.September,
		9:  time.October,
		10: time.November,
		11: time.December,
	}
	return monthMap[m]
}

// export
func lookupWeekday(day string, desiredSundayNumber int) int {
	dayNumberMap := map[string]int{
		"mon":       1,
		"monday":    1,
		"tue":       2,
		"tuesday":   2,
		"wed":       3,
		"wednesday": 3,
		"thu":       4,
		"thursday":  4,
		"fri":       5,
		"friday":    5,
		"sat":       6,
		"saturday":  6,
		"sun":       0,
		"sunday":    0,
	}

	if n, ok := dayNumberMap[strings.ToLower(day)]; ok {
		return n
	}

	return desiredSundayNumber
}

// export
func lookupRelative(rel string) (amount int, behavior int) {
	relativeNumbersMap := map[string]int{
		"back":     15,
		"front":    45,
		"last":     -1,
		"previous": -1,
		"this":     0,
		"first":    1,
		"next":     1,
		"second":   2,
		"third":    3,
		"fourth":   4,
		"fifth":    5,
		"sixth":    6,
		"seventh":  7,
		"eight":    8,
		"eighth":   8,
		"ninth":    9,
		"tenth":    10,
		"eleventh": 11,
		"twelfth":  12,
	}

	relativeBehaviorMap := map[string]int{
		"this":  1,
		"front": -1,
		"back":  0,
	}

	relativeBehaviorValue := 0

	if value, ok := relativeBehaviorMap[rel]; ok {
		relativeBehaviorValue = value
	}

	rel = strings.ToLower(rel)

	return relativeNumbersMap[rel], relativeBehaviorValue
}

// processTzCorrection converts a time zone offset (i.e. GMT-5) to minutes (i.e. 300)
// export
func processTzCorrection(tzOffset string, oldValue int) int {
	const reTzCorrectionLoose = `(?:GMT)?([+-])(\d+)(:?)(\d{0,2})`
	re := regexp.MustCompile(reTzCorrectionLoose)
	offsetGroups := re.FindStringSubmatch(tzOffset)

	sign := -1

	if strings.Contains(tzOffset, "-") {
		sign = 1
	}

	hours, err := strconv.Atoi(offsetGroups[2])

	if err != nil {
		return oldValue
	}

	var minutes int

	if strings.Contains(tzOffset, ":") && len(offsetGroups[4]) > 0 {
		minutes, err = strconv.Atoi(offsetGroups[4])

		if err != nil {
			return oldValue
		}
	}

	if !strings.Contains(tzOffset, ":") && len(offsetGroups[2]) > 2 {
		m := float64(hours % 100)
		h := float64(hours / 100)
		minutes = int(math.Floor(m))
		hours = int(math.Floor(h))
	}

	return sign * (hours*60 + minutes)
}

// export
func getUtcHour(input string) int {
	re := regexp.MustCompile(`:\\d{2}[zZ+-](\\d{2})`)
	match := re.FindStringSubmatch(input)
	if len(match) == 2 {
		hourMatch := match[1]
		hour, _ := strconv.Atoi(hourMatch)
		if hour > -24 && hour < 24 {
			return hour
		}
	}
	return 0
}

// export
func StructCopy(src, dst any) {
	if src == nil || dst == nil {
		return
	}

	structCopy(reflect.ValueOf(src), reflect.ValueOf(dst))
}

// structCopy 复制 struct 对象
// export
func structCopy(src, dst reflect.Value) {
	st := src.Type()
	dt := dst.Type()

	if st.Kind() == reflect.Ptr {
		src = src.Elem()
		st = st.Elem()
	}

	if dt.Kind() == reflect.Ptr {
		dst = dst.Elem()
		dt = dt.Elem()
	}

	// Only struct are supported
	if st.Kind() != reflect.Struct || dt.Kind() != reflect.Struct {
		return
	}
	var field reflect.Value
	for i := 0; i < st.NumField(); i++ {
		if !st.Field(i).Anonymous {
			field = dst.FieldByName(st.Field(i).Name)
			if field.IsValid() && field.CanSet() {
				field.Set(src.Field(i))
			}
		} else {
			structCopy(src.Field(i).Addr(), dst)
		}
	}
}

// Ip2Long 字符串 IP 转整型
// export
func Ip2Long(ipStr string) uint32 {
	ip := net.ParseIP(ipStr)
	if ip == nil {
		return 0
	}
	ip = ip.To4()
	if ip == nil {
		return 0
	}

	return binary.BigEndian.Uint32(ip)
}

// Long2Ip 整型转字符串 IP
// export
func Long2Ip(long uint32) string {
	ipByte := make([]byte, 4)
	binary.BigEndian.PutUint32(ipByte, long)
	ip := net.IP(ipByte)

	return ip.String()
}

// ToString 将任意一个类型转换为字符串
// export
func ToString(value any) string {
	return fmt.Sprintf("%v", value)
}

// ToInt 数字或字符串转 int 类型
// export
func ToInt(value any) int {
	switch v := value.(type) {
	case int8:
		return int(v)
	case uint8:
		return int(v)
	case uint16:
		return int(v)
	case int16:
		return int(v)
	case int32:
		return int(v)
	case int:
		return v
	case string:
		i, _ := strconv.Atoi(v)
		return i
	}

	return 0
}

// ToLong ToInt64 别名, 数字或字符串转 int64
// export
func ToLong(value any) int64 {
	return ToInt64(value)
}

// ToBool 字符串转 bool 类型
// export
func ToBool(str string) bool {
	b, err := strconv.ParseBool(str)
	if err != nil {
		return false
	} else {
		return b
	}
}

// ToUint 数字或字符串转 uint
// export
func ToUint(value any) uint {
	switch v := value.(type) {
	case int8:
		return uint(v)
	case uint8:
		return uint(v)
	case uint16:
		return uint(v)
	case int16:
		return uint(v)
	case int32:
		return uint(v)
	case int:
		return uint(v)
	case uint:
		return v
	case string:
		i, _ := strconv.ParseUint(v, 10, 32)
		return uint(i)
	}

	return 0
}

// ToUint8 数字或字符串转 uint8
// export
func ToUint8(value any) uint8 {
	switch v := value.(type) {
	case int8:
		return uint8(v)
	case uint8:
		return v
	case string:
		i, _ := strconv.ParseUint(v, 10, 8)
		return uint8(i)
	}

	return 0
}

// ToInt64 数字或字符串转 int64
// export
func ToInt64(value any) int64 {
	switch v := value.(type) {
	case int:
		return int64(v)
	case uint8:
		return int64(v)
	case int8:
		return int64(v)
	case int16:
		return int64(v)
	case uint16:
		return int64(v)
	case int32:
		return int64(v)
	case uint32:
		return int64(v)
	case int64:
		return v
	case string:
		i, _ := strconv.ParseInt(v, 10, 64)
		return i
	}

	return 0
}

// ToFloat32 数字或字符串转 float32
// export
func ToFloat32(value any) float32 {
	switch v := value.(type) {
	case int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64:
		return float32(ToInt64(v))
	case float32:
		return v
	case float64:
		return float32(v)
	case string:
		i, _ := strconv.ParseFloat(v, 32)
		return float32(i)
	}

	return 0
}

// ToFloat64 数字或字符串转 float64
// export
func ToFloat64(value any) float64 {
	switch v := value.(type) {
	case int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64:
		return float64(ToInt64(v))
	case float32:
		return float64(v)
	case float64:
		return v
	case string:
		i, _ := strconv.ParseFloat(v, 64)
		return i
	}

	return 0
}

// ToUtf8 指定字符集转 utf-8
// export
func ToUtf8(origin []byte, encode string) ([]byte, error) {
	e, err := ianaindex.MIME.Encoding(encode)
	if err != nil {
		return nil, err
	}

	if e == nil {
		return nil, errors.New("unsupported encoding")
	}

	r := transform.NewReader(bytes.NewReader(origin), e.NewDecoder())
	s, err := io.ReadAll(r)
	if err != nil {
		return nil, err
	}

	return s, nil
}

// Utf8To utf-8 转指定字符集
// export
func Utf8To(utf8 []byte, encode string) ([]byte, error) {
	e, err := ianaindex.MIME.Encoding(encode)
	if err != nil {
		return nil, err
	}

	r := transform.NewReader(bytes.NewReader(utf8), e.NewEncoder())
	s, err := io.ReadAll(r)
	if err != nil {
		return nil, err
	}

	return s, nil
}

// ToJson 将对象转换为 Json 字符串
// export
func ToJson(object any) string {
	res, err := json.Marshal(object)
	if err != nil {
		return ""
	}

	return String(res)
}

// ToJsonIndent 将对象转换为 Json 字符串, 带缩进
// export
func ToJsonIndent(object any) string {
	res, err := json.MarshalIndent(object, "", "  ")
	if err != nil {
		return ""
	}

	return String(res)
}

// ToDuration 将数字、字符串转换为 time.Duration，默认是 ns, 如果是字符串，支持 ns,ms,us,s,m,h
// export
func ToDuration(value any) time.Duration {
	switch v := value.(type) {
	case time.Duration:
		return v
	case int, int64, int32, int16, int8, uint, uint64, uint32, uint16, uint8:
		return time.Duration(ToInt64(v))
	case float32, float64:
		return time.Duration(ToFloat64(v))
	case string:
		if strings.ContainsAny(v, "nsuµmh") {
			d, _ := time.ParseDuration(v)
			return d
		} else {
			d, _ := time.ParseDuration(v + "ns")
			return d
		}
	}

	return 0
}

// ToDurationMs 将数字、字符串转换为 time.Duration，默认是 ms, 如果是字符串，支持 ns,ms,us,s,m,h
// export
func ToDurationMs(value any) time.Duration {
	switch v := value.(type) {
	case time.Duration:
		return v
	case int, int64, int32, int16, int8, uint, uint64, uint32, uint16, uint8:
		return ToDuration(value) * time.Millisecond
	case float32, float64:
		return ToDuration(value) * time.Millisecond
	case string:
		if strings.ContainsAny(v, "nsuµmh") {
			d, _ := time.ParseDuration(v)
			return d
		} else {
			d, _ := time.ParseDuration(v + "ms")
			return d
		}
	}

	return 0
}

// export
func Encrypt(texto, clave string) (string, error) {
	// Convertir la clave a bytes
	key := []byte(clave)

	// Crear un bloque AES
	block, err := aes.NewCipher(key)
	if err != nil {
		return "", err
	}

	// Crear un vector de inicialización (IV)
	iv := make([]byte, aes.BlockSize)
	if _, err := io.ReadFull(crand.Reader, iv); err != nil {
		return "", err
	}

	// Asegurarse de que el texto tenga un tamaño múltiplo del bloque
	paddedTexto := []byte(texto)
	if len(paddedTexto)%aes.BlockSize != 0 {
		padding := aes.BlockSize - len(paddedTexto)%aes.BlockSize
		paddedTexto = append(paddedTexto, bytes.Repeat([]byte{byte(padding)}, padding)...)
	}

	// Cifrar el texto
	ciphertext := make([]byte, aes.BlockSize+len(paddedTexto))
	copy(ciphertext[:aes.BlockSize], iv) // Almacenar el IV al inicio
	mode := cipher.NewCBCEncrypter(block, iv)
	mode.CryptBlocks(ciphertext[aes.BlockSize:], paddedTexto)

	return hex.EncodeToString(ciphertext), nil
}

// DescifrarAES descifra el texto cifrado usando AES con la clave secreta
// export
func Decrypt(textoCifrado, clave string) (string, error) {
	// Convertir la clave a bytes
	key := []byte(clave)

	// Crear un bloque AES
	block, err := aes.NewCipher(key)
	if err != nil {
		return "", err
	}

	// Decodificar el texto cifrado de hexadecimal a bytes
	ciphertext, err := hex.DecodeString(textoCifrado)
	if err != nil {
		return "", err
	}

	// Extraer el IV del inicio
	if len(ciphertext) < aes.BlockSize {
		return "", fmt.Errorf("texto cifrado demasiado corto")
	}
	iv := ciphertext[:aes.BlockSize]
	ciphertext = ciphertext[aes.BlockSize:]

	// Descifrar el texto
	decrypted := make([]byte, len(ciphertext))
	mode := cipher.NewCBCDecrypter(block, iv)
	mode.CryptBlocks(decrypted, ciphertext)

	// Deshacer el padding
	padding := decrypted[len(decrypted)-1]
	decrypted = decrypted[:len(decrypted)-int(padding)]

	return string(decrypted), nil
}

// export
func GetHash(input string) string {
	// Crear un nuevo hash SHA-256
	hash := sha256.New()
	// Escribir el string en el hash
	hash.Write([]byte(input))
	// Obtener el resultado del hash
	return hex.EncodeToString(hash.Sum(nil))
}

// export
func ReadExcel(excelFile string, sheetName string) [][]string {
	f, err := excelize.OpenFile(excelFile)
	if err != nil {
		fmt.Println(err)
		return nil
	}
	rows, err := f.GetRows(sheetName)
	if err != nil {
		fmt.Println(err)
		return nil
	}
	defer func() {
		f.Close()
	}()
	return rows
}

// export
func CreateExcelP(headers []string, data [][]interface{}, filename string) error {
	// Crear un nuevo archivo Excel
	f := excelize.NewFile()

	// Agregar encabezados
	for i, header := range headers {
		cell := fmt.Sprintf("%s%d", string('A'+i), 1) // A1, B1, C1, ...
		f.SetCellValue("Sheet1", cell, header)
	}

	// Agregar datos
	for r, row := range data {
		for c, value := range row {
			cell := fmt.Sprintf("%s%d", string('A'+c), r+2) // A2, B2, C2, ...
			// Convertir el valor a string antes de establecerlo en la celda
			f.SetCellValue("Sheet1", cell, value)
		}
	}

	// Guardar el archivo
	if err := f.SaveAs(filename); err != nil {
		return err
	}

	return nil
}

// export
func CreateExcel(data []map[string]interface{}, filename string) string {
	archivo := fmt.Sprintf("static/%s.xlsx", filename)

	// Asegúrate de que el directorio existe
	err := os.MkdirAll("static", os.ModePerm)
	if err != nil {
		return fmt.Sprintf("ERROR al crear directorio: %v", err)
	}

	// Crear un nuevo archivo Excel
	f := excelize.NewFile()
	sheetName := "Sheet1"

	// Agregar encabezados
	headers := make([]string, 0)
	for key := range data[0] {
		headers = append(headers, key)
	}
	for i, header := range headers {
		f.SetCellValue(sheetName, fmt.Sprintf("%s%d", string('A'+i), 1), header)
	}

	// Agregar datos
	for rowIndex, row := range data {
		for colIndex, header := range headers {
			f.SetCellValue(sheetName, fmt.Sprintf("%s%d", string('A'+colIndex), rowIndex+2), row[header])
		}
	}

	// Guardar el archivo
	if err := f.SaveAs(archivo); err != nil {
		return fmt.Sprintf("ERROR al guardar archivo: %v", err)
	}

	return filename
}

// export
func ConvertToJSON(data interface{}) (string, error) {
	jsonData, err := json.Marshal(data)
	if err != nil {
		return "", fmt.Errorf("error al convertir a JSON: %v", err)
	}
	return string(jsonData), nil
}

// export
func ConvertFromJSON(jsonStr string) (interface{}, error) {
	var data interface{}
	err := json.Unmarshal([]byte(jsonStr), &data)
	if err != nil {
		return nil, fmt.Errorf("error al convertir de JSON: %v", err)
	}
	return data, nil
}

// export
func ToJSON(data interface{}) (string, error) {
	// Convertir a JSON con sangrías
	jsonData, err := json.MarshalIndent(data, "", "    ")
	if err != nil {
		return "", err
	}
	return string(jsonData), nil
}

// export
func FromJSON(jsonStr string) (interface{}, error) {
	var data interface{}
	err := json.Unmarshal([]byte(jsonStr), &data)
	if err != nil {
		return nil, fmt.Errorf("error al convertir de JSON: %v", err)
	}
	return data, nil
}

// export
func ReadJsonFile(nombreArchivo string) (map[string]interface{}, error) {
	archivo, err := os.Open(nombreArchivo)
	if err != nil {
		return nil, err
	}
	defer archivo.Close()

	var datos map[string]interface{}
	decodificador := json.NewDecoder(archivo)
	err = decodificador.Decode(&datos)
	if err != nil {
		return nil, err
	}
	return datos, nil
}

// export
func NodeRequest(method string, params []interface{}) (map[string]interface{}, error) {
	confs, err := LeerConfiguracionNode("Kron.conf")
	if err != nil {
		return nil, err
	}

	url := fmt.Sprintf("http://127.0.0.1:%s/", confs.RpcPort)
	headers := map[string]string{"content-type": "text/plain"}

	data := map[string]interface{}{
		"jsonrpc": "1.0",
		"id":      "curltest",
		"method":  method,
		"params":  params,
	}

	jsonData, err := json.Marshal(data)
	if err != nil {
		return nil, err
	}

	req, err := http.NewRequest("POST", url, bytes.NewBuffer(jsonData))
	if err != nil {
		return nil, err
	}

	for key, value := range headers {
		req.Header.Set(key, value)
	}

	// Autenticación básica
	req.SetBasicAuth(confs.RpcUser, confs.RpcPassword)

	client := &http.Client{}
	response, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer response.Body.Close()

	var result map[string]interface{}
	if err := json.NewDecoder(response.Body).Decode(&result); err != nil {
		return nil, err
	}

	return result, nil
}

type Config struct {
	RpcUser     string
	RpcPassword string
	RpcPort     string
}

// export
func LeerConfiguracionNode(filename string) (Config, error) {
	var conf Config
	file, err := os.Open(filename)
	if err != nil {
		return conf, err
	}
	defer file.Close()

	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		linea := scanner.Text()
		var clave, valor string
		fmt.Sscanf(linea, "%s=%s", &clave, &valor)
		switch clave {
		case "rpcuser":
			conf.RpcUser = valor
		case "rpcpassword":
			conf.RpcPassword = valor
		case "rpcport":
			conf.RpcPort = valor
		}
	}
	return conf, scanner.Err()
}

// export
func NodeRequestKron(method string, params []interface{}) (interface{}, error) {
	confs, err := LeerConfiguracionNode("Kron.conf")
	if err != nil {
		return nil, err
	}

	url := fmt.Sprintf("http://127.0.0.1:%s/", confs.RpcPort)
	headers := map[string]string{"content-type": "text/plain"}

	data := map[string]interface{}{
		"jsonrpc": "1.0",
		"id":      "curltest",
		"method":  method,
		"params":  params,
	}

	jsonData, err := json.Marshal(data)
	if err != nil {
		return nil, err
	}

	req, err := http.NewRequest("POST", url, bytes.NewBuffer(jsonData))
	if err != nil {
		return nil, err
	}

	for key, value := range headers {
		req.Header.Set(key, value)
	}

	// Autenticación básica
	req.SetBasicAuth(confs.RpcUser, confs.RpcPassword)

	client := &http.Client{}
	response, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer response.Body.Close()

	var result map[string]interface{}
	if err := json.NewDecoder(response.Body).Decode(&result); err != nil {
		return nil, err
	}

	return result["result"], nil
}

// export
func ReqTor(payload map[string]interface{}, domain string, ruta string) (map[string]interface{}, error) {
	h := map[string]string{
		"User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/104.0.0.0 Safari/537.36",
	}

	client := &http.Client{
		Transport: &http.Transport{
			Proxy: http.ProxyURL(&url.URL{
				Scheme: "socks5h",
				Host:   "localhost:9050",
			}),
		},
		Timeout: 30 * time.Second,
	}

	payloadBytes, err := json.Marshal(payload)
	if err != nil {
		return nil, err
	}

	req, err := http.NewRequest("POST", ""+domain+ruta, bytes.NewBuffer(payloadBytes))
	if err != nil {
		return nil, err
	}

	for key, value := range h {
		req.Header.Set(key, value)
	}

	res, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer res.Body.Close()

	var result map[string]interface{}
	if err := json.NewDecoder(res.Body).Decode(&result); err != nil {
		return nil, err
	}

	fmt.Println(result)
	return result, nil
}

// export
func ReqTorGet(payload map[string]interface{}, domain string, ruta string) (map[string]interface{}, error) {
	h := map[string]string{
		"User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/104.0.0.0 Safari/537.36",
	}

	client := &http.Client{
		Transport: &http.Transport{
			Proxy: http.ProxyURL(&url.URL{
				Scheme: "socks5h",
				Host:   "localhost:9050",
			}),
		},
		Timeout: 30 * time.Second,
	}

	// Convertir el payload a JSON
	payloadBytes, err := json.Marshal(payload)
	if err != nil {
		return nil, err
	}

	req, err := http.NewRequest("GET", ""+domain+ruta, bytes.NewBuffer(payloadBytes))
	if err != nil {
		return nil, err
	}

	for key, value := range h {
		req.Header.Set(key, value)
	}

	res, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer res.Body.Close()

	var result map[string]interface{}
	if err := json.NewDecoder(res.Body).Decode(&result); err != nil {
		return nil, err
	}

	fmt.Println(result)
	return result, nil
}

// export
func GetHTML(url string) (string, error) {
	// Realizar la solicitud HTTP
	respuesta, err := http.Get(url)
	if err != nil {
		return "", err
	}
	defer respuesta.Body.Close()

	// Leer el cuerpo de la respuesta
	html, err := io.ReadAll(respuesta.Body)
	if err != nil {
		return "", err
	}

	return string(html), nil
}

// export
func ServeHTML() {
	// Manejador personalizado para servir archivos estáticos
	http.Handle("/static/", http.StripPrefix("/static/", http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		filePath := filepath.Join("static", r.URL.Path[len("/static/"):])
		http.ServeFile(w, r, filePath)

		// Establecer el tipo MIME
		ext := filepath.Ext(filePath)
		switch ext {
		case ".js":
			w.Header().Set("Content-Type", "application/javascript")
		case ".css":
			w.Header().Set("Content-Type", "text/css")
			// Agrega más tipos MIME según sea necesario
		}
	})))

	// Manejar la ruta raíz (/) y servir el archivo index.html desde la carpeta templates
	http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		ip := r.RemoteAddr
		host, _, err := net.SplitHostPort(ip)
		if err != nil {
			fmt.Println("Error al obtener la IP:", err)
			return
		}

		// Convertir a IPv4 si es necesario
		parsedIP := net.ParseIP(host)
		if parsedIP != nil && parsedIP.To4() != nil {
			fmt.Println("Conectado desde IP:", parsedIP.To4().String())
		} else {
			fmt.Println("Conectado desde IP:", host) // IPv6 o no se puede convertir
		}
		http.ServeFile(w, r, "templates/index.html")
	})
}

// export
func RunServer(port string) {
	fmt.Println("Server running at ", "http://0.0.0.0:"+port)
	err := http.ListenAndServe("0.0.0.0:"+port, nil)
	if err != nil {
		panic(err)
	}
}

// export
func GetHTMLTor(urlStr string) (string, error) {
	// Configurar el proxy de Tor
	proxyURL, err := url.Parse("socks5h://127.0.0.1:9050")
	if err != nil {
		return "", err
	}

	// Crear un transport con el proxy
	transport := &http.Transport{
		Proxy: http.ProxyURL(proxyURL),
	}

	// Crear un cliente HTTP con el transporte
	cliente := &http.Client{
		Transport: transport,
	}

	// Realizar la solicitud HTTP
	respuesta, err := cliente.Get(urlStr)
	if err != nil {
		return "", err
	}
	defer respuesta.Body.Close()

	// Leer el cuerpo de la respuesta
	html, err := io.ReadAll(respuesta.Body)
	if err != nil {
		return "", err
	}

	return string(html), nil
}

// export
func Assoc(dsn string, consulta string) ([]map[string]interface{}, error) {

	// Conectar a la base de datos
	db, err := sql.Open("mysql", dsn)
	if err != nil {
		return nil, err
	}
	defer db.Close() // Cerrar la conexión al final de la función
	filas, err := db.Query(consulta)
	if err != nil {
		return nil, err
	}
	defer filas.Close()

	columnas, err := filas.Columns()
	if err != nil {
		return nil, err
	}

	// Crear un slice para almacenar los registros
	var registros []map[string]interface{}

	// Preparar un slice para almacenar los valores de cada fila
	valores := make([]interface{}, len(columnas))
	punteros := make([]interface{}, len(columnas))
	for i := range punteros {
		punteros[i] = &valores[i]
	}

	// Iterar sobre las filas
	for filas.Next() {
		err := filas.Scan(punteros...)
		if err != nil {
			return nil, err
		}

		// Crear un mapa para la fila actual
		fila := make(map[string]interface{})
		for i, col := range columnas {
			// Convertir valores de tipo []byte a string
			if b, ok := valores[i].([]byte); ok {
				fila[col] = string(b)
			} else {
				fila[col] = valores[i]
			}
		}

		registros = append(registros, fila)
	}

	return registros, nil
}

func DatabaseConnectionData(usuario, contrasena, host, puerto, baseDatos string) string {
	dsn := fmt.Sprintf("%s:%s@tcp(%s:%s)/%s", usuario, contrasena, host, puerto, baseDatos)
	return dsn
}

// ObtenerRegistros obtiene registros de la base de datos y los devuelve como un slice de mapas
// export
func AssocSecure(dsn, consulta string, parametros ...interface{}) ([]map[string]interface{}, error) {
	// Construir la cadena de conexión

	// Conectar a la base de datos
	db, err := sql.Open("mysql", dsn)
	if err != nil {
		return nil, err
	}
	defer db.Close() // Cerrar la conexión al final de la función

	// Ejecutar la consulta parametrizada
	filas, err := db.Query(consulta, parametros...)
	if err != nil {
		return nil, err
	}
	defer filas.Close()

	columnas, err := filas.Columns()
	if err != nil {
		return nil, err
	}

	// Crear un slice para almacenar los registros
	var registros []map[string]interface{}

	// Preparar un slice para almacenar los valores de cada fila
	valores := make([]interface{}, len(columnas))
	punteros := make([]interface{}, len(columnas))
	for i := range punteros {
		punteros[i] = &valores[i]
	}

	// Iterar sobre las filas
	for filas.Next() {
		err := filas.Scan(punteros...)
		if err != nil {
			return nil, err
		}

		// Crear un mapa para la fila actual
		fila := make(map[string]interface{})
		for i, col := range columnas {
			// Convertir valores de tipo []byte a string
			if b, ok := valores[i].([]byte); ok {
				fila[col] = string(b)
			} else {
				fila[col] = valores[i]
			}
		}

		registros = append(registros, fila)
	}

	return registros, nil
}

// export
func AssocSqlite3(dbName string, consulta string) ([]map[string]interface{}, error) {
	// Abrir la conexión a la base de datos
	db, err := sql.Open("sqlite3", dbName)
	if err != nil {
		return nil, err
	}
	defer db.Close() // Asegurar que se cierre la conexión al final

	filas, err := db.Query(consulta)
	if err != nil {
		return nil, err
	}
	defer filas.Close()

	columnas, err := filas.Columns()
	if err != nil {
		return nil, err
	}

	// Crear un slice para almacenar los registros
	var registros []map[string]interface{}

	// Preparar un slice para almacenar los valores de cada fila
	valores := make([]interface{}, len(columnas))
	punteros := make([]interface{}, len(columnas))
	for i := range punteros {
		punteros[i] = &valores[i]
	}

	// Iterar sobre las filas
	for filas.Next() {
		err := filas.Scan(punteros...)
		if err != nil {
			return nil, err
		}

		// Crear un mapa para la fila actual
		fila := make(map[string]interface{})
		for i, col := range columnas {
			// Manejar valores nulos y convertir []byte a string
			switch v := valores[i].(type) {
			case []byte:
				fila[col] = string(v)
			case nil:
				fila[col] = nil // Manejar valores nulos
			default:
				fila[col] = v
			}
		}

		registros = append(registros, fila)
	}

	// Verificar errores en la iteración de filas
	if err := filas.Err(); err != nil {
		return nil, err
	}

	return registros, nil
}

// export
func QuerySecureSqlite3(dbName string, consulta string, parametros ...interface{}) (sql.Result, error) {
	// Conectar a la base de datos
	db, err := sql.Open("sqlite3", dbName)
	if err != nil {
		return nil, err
	}
	defer db.Close() // Cerrar la conexión al final de la función

	// Ejecutar la consulta UPDATE parametrizada
	resultado, err := db.Exec(consulta, parametros...)
	if err != nil {
		return nil, err
	}

	return resultado, nil
}

// EjecutarUpdate ejecuta una consulta UPDATE en la base de datos
// export
func QuerySecure(dsn, consulta string, parametros ...interface{}) (sql.Result, error) {
	// Construir la cadena de conexión
	// Conectar a la base de datos
	db, err := sql.Open("mysql", dsn)
	if err != nil {
		return nil, err
	}
	defer db.Close() // Cerrar la conexión al final de la función

	// Ejecutar la consulta UPDATE parametrizada
	resultado, err := db.Exec(consulta, parametros...)
	if err != nil {
		return nil, err
	}

	return resultado, nil
}

// export
func ExecuteQuery(dsn, consulta string, parametros ...interface{}) (sql.Result, error) {
	// Conectar a la base de datos
	db, err := sql.Open("mysql", dsn)
	if err != nil {
		return nil, err
	}
	defer db.Close() // Cerrar la conexión al final de la función

	// Ejecutar la consulta INSERT parametrizada
	resultado, err := db.Exec(consulta, parametros...)
	if err != nil {
		return nil, err
	}

	return resultado, nil
}

// export
func ExecuteQuerySqlite3(dbName string, consulta string, parametros ...interface{}) (sql.Result, error) {
	// Conectar a la base de datos
	db, err := sql.Open("sqlite3", dbName)
	if err != nil {
		return nil, err
	}
	defer db.Close() // Cerrar la conexión al final de la función

	// Ejecutar la consulta INSERT parametrizada
	resultado, err := db.Exec(consulta, parametros...)
	if err != nil {
		return nil, err
	}

	return resultado, nil
}

// export
func AlterTable(dsn, instruccion string) (sql.Result, error) {

	// Conectar a la base de datos
	db, err := sql.Open("mysql", dsn)
	if err != nil {
		return nil, err
	}
	defer db.Close() // Cerrar la conexión al final de la función

	// Ejecutar la instrucción SQL
	resultado, err := db.Exec(instruccion)
	if err != nil {
		return nil, err
	}

	return resultado, nil
}

// export
func ExecuteQueryServer(usuario, contrasena, host, puerto, instruccion string) (sql.Result, error) {
	// Construir la cadena de conexión
	dsn := fmt.Sprintf("%s:%s@tcp(%s:%s)/", usuario, contrasena, host, puerto)

	// Conectar a la base de datos
	db, err := sql.Open("mysql", dsn)
	if err != nil {
		return nil, err
	}
	defer db.Close() // Cerrar la conexión al final de la función

	// Ejecutar la instrucción SQL
	resultado, err := db.Exec(instruccion)
	if err != nil {
		return nil, err
	}

	return resultado, nil
}

// export
func AlterTableSqlite3(dbName string, instruccion string) (sql.Result, error) {
	// Conectar a la base de datos
	db, err := sql.Open("sqlite3", dbName)
	if err != nil {
		return nil, err
	}
	defer db.Close() // Cerrar la conexión al final de la función

	// Ejecutar la instrucción SQL
	resultado, err := db.Exec(instruccion)
	if err != nil {
		return nil, err
	}

	return resultado, nil
}

func GetScrappedContent(etiqueta string, cuerpo io.Reader) ([]string, error) {
	// Crear un nuevo documento a partir del cuerpo HTML
	doc, err := goquery.NewDocumentFromReader(cuerpo)
	if err != nil {
		return nil, err
	}

	// Slice para almacenar los contenidos encontrados
	var contenidos []string

	// Buscar los elementos de la etiqueta especificada
	doc.Find(etiqueta).Each(func(index int, item *goquery.Selection) {
		texto := item.Text()
		title, _ := item.Attr("href")
		contenidos = append(contenidos, texto)
		contenidos = append(contenidos, title)
	})

	return contenidos, nil
}

func CreateTorProxy(port string) (*http.Client, error) {
	proxyURL, err := url.Parse("socks5h://localhost:" + port)
	if err != nil {
		return nil, err
	}

	client := &http.Client{
		Transport: &http.Transport{
			Proxy: http.ProxyURL(proxyURL),
		},
		Timeout: 30 * time.Second,
	}
	return client, nil
}
