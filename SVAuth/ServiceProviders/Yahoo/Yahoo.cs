﻿using Microsoft.AspNetCore.Routing;
using System;
using System.Net.Http;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using BytecodeTranslator.Diagnostics;
using Newtonsoft.Json.Linq;
using System.Threading.Tasks;
using Newtonsoft.Json;
using Microsoft.AspNetCore.Http;
using SVX;
using SVAuth.OpenID20;
using System.Text.RegularExpressions;

namespace SVAuth.ServiceProviders.Yahoo
{
    public class YahooAppRegistration
    {
        public string clientID;
        public string clientSecret;
    }
    public class AuthenticationRequest : OpenID20.AuthenticationRequest
    {
        [JsonProperty("openid.ns.oauth")]
        public string openid__ns__oauth;
        [JsonProperty("openid.oauth.consumer")]
        public string openid__oauth__consumer;

        /*attribute exchange*/
        [JsonProperty("openid.ns.ax")]
        public string openid__ns__ax;
        [JsonProperty("openid.ax.mode")]
        public string openid__ax__mode;
        [JsonProperty("openid.ax.type.email")]
        public string openid__ax__type__email;
        [JsonProperty("openid.ax.type.fullname")]
        public string openid__ax__type__fullname;
        [JsonProperty("openid.ax.required")]
        public string openid__ax__required;

    }

    public class FieldsExpectedToBeSigned : OpenID20.FieldsExpectedToBeSigned
    {
        [JsonProperty("openid.oauth.request_token")]
        public string openid__oauth__request_token;
        [JsonProperty("openid.ax.value.email")]
        public string openid__ax__value__email;
        [JsonProperty("openid.ax.type.email")]
        public string openid__ax__type__email;
        [JsonProperty("openid.ax.value.fullname")]
        public string openid__ax__value__fullname;
        [JsonProperty("openid.ax.type.fullname")]
        public string openid__ax__type__fullname;
    }

    public class AuthenticationResponse : OpenID20.AuthenticationResponse
    {
       // public FieldsExpectedToBeSigned FieldsExpectedToBeSigned;
    }

    public class UserProfile : GenericAuth.UserProfile
    {
        public string Email;
        public string FullName;
        public string Identity;
    }

    public class YahooSignedFieldsVerifier : OpenID20.OpenID20SignedFieldsVerifier
    {
        public string SignatureValidationUrl;

        public override OpenID20.FieldsExpectedToBeSigned UnReflectFieldsExpectedToBeSigned(JObject obj)
        {
            return Utils.UnreflectObject<FieldsExpectedToBeSigned>(obj);
        }

        protected override OpenID20.FieldsExpectedToBeSigned RawVerifyAndExtract(string secretValue)
        {
            //To be more confident, we require a precondition when calling this method:  openid.ns == "http://specs.openid.net/auth/2.0"
            //Currently, this condition is checked in a method inside OpenID20.cs, which is not natural, and might be dangerous if other developers add 
            //another method to call this Yahoo signature validation method.
            //ToDo: check openid.ns == "http://specs.openid.net/auth/2.0"  in this method.
            string patternOpenIdMode = @"openid\.mode=.*?\&";
            string patternFirstQuestionMark = @"^\?";

            string sanitizedSecretValue = Regex.Replace(secretValue, patternOpenIdMode, "");
            sanitizedSecretValue = Regex.Replace(sanitizedSecretValue, patternFirstQuestionMark, "");

            // build request
            var RawRequestUrl = SignatureValidationUrl + "?openid.mode=check_authentication&" + sanitizedSecretValue;

            var rawReq = new HttpRequestMessage(HttpMethod.Get, RawRequestUrl);
            var RawResponse = Utils.PerformHttpRequestAsync(rawReq).Result;

            string response_string = RawResponse.Content.ReadAsStringAsync().Result;
            string aLine = null;
            System.IO.StringReader strReader = new System.IO.StringReader(response_string);
            while (true)
            {
                aLine = strReader.ReadLine();
                if (aLine != null)
                {
                    if (aLine == "is_valid:true")
                        break;
                }
                else break;
            }
            if (RawResponse.StatusCode != System.Net.HttpStatusCode.OK || aLine==null)
                throw new Exception(); // TODO: Somewhere in the svAuth app we should catch this exception
            // When REDACTED tried to pass a malicious secretValue input, this exception was raised and not being caught
            // and the svAuth server just hang

            return RawExtractUnverified(secretValue);
        }

        public YahooSignedFieldsVerifier()
        {
            IdPPrincipal = Yahoo_IdP.YahooPrincipal;
        }

    }

    [BCTOmit]
    public class MessageStructures:OpenID20.MessageStructures
    {
       internal YahooSignedFieldsVerifier YahooSignedFieldsVerifier = new YahooSignedFieldsVerifier()
                { SignatureValidationUrl= "https://open.login.yahooapis.com/openid/op/auth" };
        protected override OpenID20.OpenID20SignedFieldsVerifier getOpenID20SignedFieldsVerifier() { return YahooSignedFieldsVerifier; }

        public MessageStructures(SVX.Entity idpPrincipal) : base(idpPrincipal) 
        {            
        }
    }
    public class Yahoo_RP : OpenID20.RelyingParty
    {
        public Yahoo_RP(SVX.Entity rpPrincipal, string Yahoo_Endpoint=null, string return_to_uri1=null, string stateKey = null)
        : base(rpPrincipal, Yahoo_Endpoint, return_to_uri1, stateKey)
        {
        }
        protected override OpenID20.ModelOpenID20AuthenticationServer CreateModelOpenID20AuthenticationServer()
        {
            return new Yahoo_IdP(Yahoo_IdP.YahooPrincipal);
        }
        public override OpenID20.MessageStructures GetMessageStructures()
        {
            return new MessageStructures(Yahoo_IdP.YahooPrincipal);
        }
        public static void Init(RouteBuilder routeBuilder)
        {
            var RP = new Yahoo_RP(
                Config.config.rpPrincipal,
                "https://open.login.yahooapis.com/openid/op/auth",
                Config.config.agentRootUrl + "callback/Yahoo",
                Config.config.stateSecretKey);
            routeBuilder.MapRoute("login/Yahoo", RP.Login_StartAsync);
            routeBuilder.MapRoute("callback/Yahoo", RP.Login_CallbackAsync);
        }
        public override OpenID20.AuthenticationRequest createAuthenticationRequest(SVX.Channel client)
        {
            AuthenticationRequest AuthenticationRequest = new AuthenticationRequest();
            AuthenticationRequest.openid__mode = "checkid_setup";
            AuthenticationRequest.openid__identity = "http://specs.openid.net/auth/2.0/identifier_select";
            AuthenticationRequest.openid__claimed_id = "http://specs.openid.net/auth/2.0/identifier_select";
            AuthenticationRequest.openid__assoc_handle = "blah_blah";
            AuthenticationRequest.openid__return_to = return_to_uri;
            AuthenticationRequest.openid__ns__oauth = "http://specs.openid.net/extensions/oauth/1.0";
            AuthenticationRequest.openid__oauth__consumer = Config.config.AppRegistration.Yahoo.clientID;

            // Yahoo doesn't seem to support OpenID extensions, so the next line is commented out
            //AuthenticationRequest.openid__sreg__required = "email,fullname";
            //AuthenticationRequest.openid__sreg__policy_url = "http://a.com/foo.html";

            AuthenticationRequest.openid__ns__ax = "http://openid.net/srv/ax/1.0";
            AuthenticationRequest.openid__ax__mode = "fetch_request";
            AuthenticationRequest.openid__ax__type__email = "http://axschema.org/contact/email";  //"http://schema.openid.net/contact/email"; //
            AuthenticationRequest.openid__ax__type__fullname = "http://axschema.org/namePerson";
            AuthenticationRequest.openid__ax__required = "email,fullname";

            var stateParams = new OpenID20.StateParams
            {
                client = client,
                idpPrincipal = idpParticipantId.principal
            };
            AuthenticationRequest.CSRF_state = stateGenerator.Generate(stateParams, SVX_Principal);
            return AuthenticationRequest;
        }
        public override string marshalAuthenticationRequest(OpenID20.AuthenticationRequest AuthenticationRequest)
        {
            return IdP_OpenID20_Uri + "?" + Utils.ObjectToUrlEncodedString(AuthenticationRequest);
        }
        [BCTOmit]
        public override OpenID20.AuthenticationResponse parse_AuthenticationResponse(HttpContext context)
        {
            OpenID20.AuthenticationResponse AuthenticationResponse;
            string arg_string;
            if (context.Request.Method.ToLower() == "get")
            {
                AuthenticationResponse = (OpenID20.AuthenticationResponse)Utils.ObjectFromQuery(context.Request.Query, typeof(AuthenticationResponse));
                arg_string = context.Request.QueryString.Value;
            }
            else
            {
                AuthenticationResponse = (OpenID20.AuthenticationResponse)Utils.ObjectFromFormPost(context.Request.Form, typeof(AuthenticationResponse));
                arg_string = context.Request.QueryString.Value;
                foreach (string key in context.Request.Form.Keys)
                {
                    arg_string += "&" + key + "=" + System.Net.WebUtility.UrlEncode(context.Request.Form[key]);
                }
            }
            PayloadSecret<OpenID20.FieldsExpectedToBeSigned> SignedFields = PayloadSecret<OpenID20.FieldsExpectedToBeSigned>.Import(arg_string);
            AuthenticationResponse.FieldsExpectedToBeSigned = SignedFields;
            return AuthenticationResponse;

        }

        public override GenericAuth.AuthenticationConclusion createConclusion(OpenID20.AuthenticationResponse inputMSG)
        {
            var AuthenticationResponse = (AuthenticationResponse)inputMSG;
            var AuthConclusion = new GenericAuth.AuthenticationConclusion();
            AuthConclusion.channel = inputMSG.SVX_sender;
            var userProfile = new UserProfile();

            userProfile.UserID = inputMSG.FieldsExpectedToBeSigned.theParams.openid__identity;
            userProfile.Identity = inputMSG.FieldsExpectedToBeSigned.theParams.openid__identity;

            userProfile.Email = ((FieldsExpectedToBeSigned)inputMSG.FieldsExpectedToBeSigned.theParams).openid__ax__value__email;
            userProfile.FullName = ((FieldsExpectedToBeSigned)inputMSG.FieldsExpectedToBeSigned.theParams).openid__ax__value__fullname;

            if (inputMSG.FieldsExpectedToBeSigned.theParams.openid__return_to != return_to_uri)
                throw new Exception("return_to in the authentication response is not of this relying party.");


            //checking CSRF_state
            var stateParams = new OpenID20.StateParams
            {
                client = inputMSG.SVX_sender,
                idpPrincipal = idpParticipantId.principal
            };
            stateGenerator.Verify(stateParams, inputMSG.FieldsExpectedToBeSigned.theParams.CSRF_state);

            AuthConclusion.userProfile = userProfile;
            AuthConclusion.userProfile.Authority = "Yahoo.com";
            return AuthConclusion;
        }
    }
    public class Yahoo_IdP : OpenID20.ModelOpenID20AuthenticationServer
    {
        public static Entity YahooPrincipal = SVX.Entity.Of("open.login.yahooapis.com");
        public Yahoo_IdP(Entity idpPrincipal) : base(idpPrincipal)
        {
        }

        protected override OpenID20.MessageStructures getMessageStrctures()
        {
            return new MessageStructures(SVX_Principal);
        }

        protected override OpenID20SignedFieldsVerifier getSignedFieldsGenerator()
        {
            return new YahooSignedFieldsVerifier();
        }
    }
}


